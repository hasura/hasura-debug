{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE LambdaCase, RecordWildCards #-}
module Main where

import GHC.Debug.Client hiding (DebugM)
import GHC.Debug.Client.Monad hiding (DebugM)
import GHC.Debug.Client.Monad.Simple (DebugM(..))
import GHC.Debug.Retainers
import GHC.Debug.Fragmentation
-- import GHC.Debug.Profile
import GHC.Debug.Dominators (retainerSize)
import GHC.Debug.Snapshot
-- import GHC.Debug.Count
-- import GHC.Debug.Types.Graph (heapGraphSize, traverseHeapGraph, ppClosure)
import GHC.Debug.Types.Ptr
--import GHC.Debug.Types.Closures
import GHC.Debug.Trace
-- import GHC.Debug.ObjectEquiv
import Control.Monad.RWS
-- import Control.Monad.Identity
-- import Control.Monad.Writer
-- import qualified Data.ByteString.Char8 as B
-- import qualified Data.ByteString.Builder as B
-- import qualified Data.Text as T
-- import qualified Data.Text.IO as T
import Control.Monad.State
-- import Data.Text (Text)
-- import GHC.Exts.Heap.ClosureTypes
import qualified Data.Foldable as F

-- import Control.Monad
-- import Debug.Trace
import Control.Exception
import Control.Concurrent
-- import Control.Concurrent.Async
-- import qualified Control.Concurrent.Chan.Unagi.Bounded as Bounded
import qualified Data.IntMap as IM
-- import Data.Bitraversable
-- import Data.Monoid
-- import Control.Applicative
-- import Data.Traversable
import Data.Kind

-- import System.Process
import System.Environment
import System.IO
import Data.Tree
import Data.Maybe
import Data.Either
import Control.Arrow (first, (***))
import qualified Data.Map as Map
-- import Data.Ord
import Data.List
import Data.Function
import Data.List.NonEmpty(NonEmpty(..))
-- import Data.Function
import GHC.Generics
import GHC.Clock

import GHC.Int


-- Collect snapshot, stepping through so we have some control over memory usage:
main :: IO ()
main = do 
  hSetBuffering stdout NoBuffering 
  getArgs >>= \case
     ("--analyze-snapshot":limDirty:mbFile) -> do
       let file = case mbFile of
                    [f] -> f
                    []  -> defaultSnapshotLocation
                    _ -> error "bad args"
       -- zero indicates no limit:
       let limI = read limDirty
           lim | limI == 0 = Nothing
               | otherwise = Just limI
       snapshotRun file $
         -- pRetainingThunks
         -- pDominators lim
         -- pFragmentation
         pClusteredHeapGML (ClusterBySourceInfo True) "/tmp/per-infoTable-byLoc.gml"

     ("--take-snapshot":mbSocket) -> do
       let sockPath = case mbSocket of
             [] -> "/tmp/ghc-debug" 
             [p] -> p
             _ -> error "usage: --take-snapshot [<socket-path>]"
       -- jank: just loop until this works:
       let maxAttempts = (50 :: Int)
           loop attempt = do
             try (go sockPath) >>= \case
               Left (e :: SomeException) 
                 | attempt == maxAttempts -> do
                     print e
                     throw e
                 | otherwise -> putStr "." >> threadDelay 200_000 >> loop (attempt+1)
               Right _ -> do 
                   putStrLn $ "Snapshot created at: "<>defaultSnapshotLocation
       loop 1

     _ -> error "bad args"
  where
    go sockPath = withDebuggeeConnect sockPath $ \e -> do 
      makeSnapshot e defaultSnapshotLocation
      outputRequestLog e

-- See: https://well-typed.com/blog/2021/01/fragmentation-deeper-look/
-- TODO optionally take a GC to compact non-pinned? Maybe no point to that
pFragmentation :: Debuggee -> IO ()
pFragmentation e = do
  pause e
  (bs, pinnedCensus, mblockCensus, blockCensus) <- run e $ do
    bs <- precacheBlocks
    roots <- gcRoots
    pinnedCensus <- censusPinnedBlocks bs roots
    mblockCensus <- censusByMBlock roots
    blockCensus  <- censusByBlock roots
    -- TODO can we do this outside of `run`, i.e. can `roots` leak?
    let badPtrs = findBadPtrs pinnedCensus
    forM_ badPtrs $ \((_,ptrs),_l)-> do
      liftIO $ print "=============== fragment object ========================================================"
      -- Look for data with just a single retainer (although we need to limit
      -- at 2 for that) which we are more likely to be able to do something
      -- about:
      rs <- findRetainersOf (Just 2) roots ptrs
      case rs of
        [ ] -> liftIO $ print "no retainers... why?"
        [_,_] -> liftIO $ print "two retainers, skipping"
        [r] -> do
          cs <- dereferenceClosures r
          cs' <- mapM (quadtraverse pure dereferenceConDesc pure pure) cs
          locs <- mapM getSourceLoc cs'
          -- displayRetainerStack is arbitrary and weird...
          -- TODO could be cool to look for the last thunk in the list (highest up in retainer tree)
          -- TODO would be cool to call out the top-most line from our own codebase too
          liftIO $ displayRetainerStack 
            [ ("", zip cs' locs) ]
        _ -> error $ "findRetainersOf broken apparently"<>(show rs)

    return (bs, pinnedCensus, mblockCensus, blockCensus)
  resume e
  
  -- Output:
  putStrLn "--------------------------------"
  summariseBlocks bs
  putStrLn "---------- mega-block histogram: --------------------------------"
  printMBlockCensus mblockCensus
  putStrLn "---------- block histogram: --------------------------------"
  printBlockCensus blockCensus
  putStrLn "---------- pinned block histogram: --------------------------------"
  -- TODO is printBlockCensus correct for pinned? i.e. same size?
  printBlockCensus $ fmap (\(PinnedCensusStats (censusStats, _))-> censusStats) pinnedCensus

  putStrLn "--------------------------------"


-- print thunks and their retained size (sort of...)
pRetainingThunks :: Debuggee -> IO ()
pRetainingThunks e = do
  pause e
  runTrace e $ do
    _bs <- precacheBlocks
    liftIO $ hPutStrLn stderr "!!!!! Done precacheBlocks !!!!!"
    roots <- gcRoots
    liftIO $ hPutStrLn stderr "!!!!! Done gcRoots !!!!!"

    (totSize,_) <- flip execStateT (0, 0::Int) $ 
      traceFromM emptyTraceFunctions{closTrace = closTraceFunc} roots

    liftIO $ hPutStrLn stderr $ "!!!!! TOTAL SIZE: "<>show totSize

  where
    -- how deeply a nested thunk (i.e. with how many thunk parents) do we
    -- want to report about?:
    thunkDepthLim = 10

    closTraceFunc _ptr (DCS size clos) continue = do
      (!sizeAcc, !thunkDepth) <- get
      mbSourceInfo <- lift $ getSourceInfo $ tableId $ info clos
      case mbSourceInfo of
        Just SourceInformation{..} 
          | "THUNK" `isPrefixOf` show infoClosureType 
            && thunkDepth < thunkDepthLim -> do
               -- reset size counter for children, at one more thunk deep:
               (sizeChildren, _) <- lift $ execStateT continue (0, thunkDepth+1)
               -- For now: print weight and info to STDOUT; we can sort this later
               liftIO $ putStrLn $
                 show (getSize sizeChildren)<>"  "<>show thunkDepth<>"  "<> show mbSourceInfo
               -- We might also be the child of a THUNK, so need to accumulate
               put (sizeAcc+size+sizeChildren, thunkDepth)
        _ -> do
           -- Note a thunk or else thunkDepthLim exceeded:
           put (sizeAcc+size, thunkDepth)
           continue

----------------------------------------
-- TODO this is still non-working for GML, in that we need GML node ids to be int32 ... :(

    {-
-- Write out the heap graph to a file, in GML format
-- ( https://web.archive.org/web/20190303094704/http://www.fim.uni-passau.de:80/fileadmin/files/lehrstuhl/brandenburg/projekte/gml/gml-technical-report.pdf )
pWriteToGML :: FilePath -> Debuggee -> IO ()
pWriteToGML path e = do
  pause e
  runTrace e $ do
    _bs <- precacheBlocks
    liftIO $ hPutStrLn stderr "!!!!! Done precacheBlocks !!!!!"
    roots <- gcRoots
    liftIO $ hPutStrLn stderr "!!!!! Done gcRoots !!!!!"

    -- We start a separate thread for serializing to GML format and writing to file:
    (ioChanW, ioChanR) <- unsafeLiftIO $ Bounded.newChan 256
    outHandle <- unsafeLiftIO $ openFile path WriteMode
    -- Hacky: choose graph output format based on filename
    let writer = case dropWhile (/='.') path of
                   ".gml" -> gmlFileWriter
                   ".net" -> pajekFileWriter
                   _ -> error "Only .gml and .net (pajek) supported"
    do fileWriterThread <- unsafeLiftIO $ async $ writer outHandle ioChanR

       runIdentityT $ traceFromM emptyTraceFunctions{closTrace = closTraceFunc ioChanW} roots
       -- Wait for the writer thread to process the last bit of the graph data:
       unsafeLiftIO $ do
         Bounded.writeChan ioChanW GMLDone
         wait fileWriterThread
    unsafeLiftIO $ hClose outHandle

  where
    closTraceFunc ioChanW ptr (DCS size clos) continue = do
      lift $ do
        mbSourceInfo <- getSourceInfo $ tableId $ info clos
        unsafeLiftIO $ do
          let closureType = constrName clos
          Bounded.writeChan ioChanW $
            GMLNode{..}
          -- Map over this closure's pointer arguments, recording an edge in
          -- our closure graph
          let sendEdge = Bounded.writeChan ioChanW . GMLEdge ptr
          void $ quadtraverse pure pure pure sendEdge clos
      continue
-}

    {-
-- FIXME this doesn't actually work (node ids seemingly needed to be
-- contiguous, for one thing. Probably need to be incrementing (in which case
-- the file format seems to make no sense)
--
-- This format is obnoxious and we can't easily stream it out in constant memory
pajekFileWriter :: Handle -> Bounded.OutChan GMLPayload -> IO ()
pajekFileWriter outHandle ioChanR = do
  (minSeen, maxSeen, lenNodes, nodes, edges) <- go maxBound minBound 0 [] []
  print ("!!!!!!!!!!!!!!!!!!!!!!!!!", minSeen, maxSeen, maxSeen - minSeen)
  let write = hPutStrLn outHandle
  write $ "*Vertices "<> show lenNodes
  forM_ nodes $ \n-> write (show n<> " "<>show (show n)) -- e.g. 234 "234"
  write "*Edges"
  forM_ edges $ \(n0, n1) -> write (show n0<>" "<>show n1)
  where
    go !minSeen !maxSeen !lenNodes !nodes !edges = do
      Bounded.readChan ioChanR >>= \case
        GMLDone -> return (minSeen, maxSeen, lenNodes, nodes, edges)
        GMLEdge (ClosurePtr !fromW) (ClosurePtr !toW) ->
          go minSeen maxSeen lenNodes nodes ((fromW,toW):edges)
        GMLNode _ (ClosurePtr !n) _ _ -> 
          go (minSeen `min` n) (maxSeen `max` n) (lenNodes+1) (n:nodes) edges
-}

    {-
-- This handles writing the graph to 'outFile' in GML format, while trying to
-- buffer writes efficiently
gmlFileWriter :: Handle -> Bounded.OutChan GMLPayload -> IO ()
gmlFileWriter outHandle ioChanR = do
  writeOpenGML
  pop >>= goWriteBatch [] batchSize
  writeCloseGML
  where
    batchSize = 100 -- TODO tune me?

    pop = Bounded.readChan ioChanR
    write = B.hPutBuilder outHandle
    bShow :: (Show a) => a -> B.Builder
    bShow = bStr . show
    bStr = B.byteString . B.pack

    goWriteBatch payloadStack n GMLDone = 
      writeNodesEdges payloadStack -- terminal case

    -- write this batch out and continue:
    goWriteBatch payloadStack 0 p = do
      writeNodesEdges (p:payloadStack)
      pop >>= goWriteBatch [] batchSize

    -- keep accumulating:
    goWriteBatch payloadStack n p = do
      pop >>= goWriteBatch (p:payloadStack) (n-1)
      
    -- NOTE: GML is defined as a 7-bit ascii serialization. We'll just use
    -- ByteString.Char8 for now.
    writeOpenGML =
      write $ "graph [\n"
           <> "comment \"this is a graph in GML format\"\n"
           <> "directed 1\n"
    writeCloseGML =
      write $ "]\n"

    writeNodesEdges = write . mconcat . map ser where
      ser = \case
        GMLDone -> error "impossible"
        GMLNode{..} ->
             "node [\n"
          <> "id " <> bShowPtr ptr <> "\n"
          <> "tp " <> bShow closureType <> "\n"
          <> "sz " <> bShow (getSize size) <> "\n"
          <> "]\n"
        GMLEdge{..} ->
             "edge [\n"
          <> "source "<> bShowPtr ptrFrom <> "\n"
          <> "target "<> bShowPtr ptrTo   <> "\n"
          <> "]\n"
        where bShowPtr (ClosurePtr w) = bShow w

-- | Communication with our GML file writer thread
data GMLPayload
  = GMLNode{
        mbSourceInfo :: !(Maybe SourceInformation)
      , ptr :: !ClosurePtr
      -- ^ id referenced by GMLEdge
      , size :: !Size
      , closureType :: !String
      }
  | GMLEdge{
        ptrFrom :: !ClosurePtr
      , ptrTo   :: !ClosurePtr
      }
  | GMLDone
  -- ^ We've finished traversing the heap, chan can be closed
-}

-- --------------------------------------------------
-- Utility crap
constrName :: (HasConstructor (Rep a), Generic a)=> a -> String
constrName = genericConstrName . from 

class HasConstructor (f :: Type -> Type) where
  genericConstrName :: f x -> String

instance HasConstructor f => HasConstructor (D1 c f) where
  genericConstrName (M1 x) = genericConstrName x

instance (HasConstructor x, HasConstructor y) => HasConstructor (x :+: y) where
  genericConstrName (L1 l) = genericConstrName l
  genericConstrName (R1 r) = genericConstrName r

instance Constructor c => HasConstructor (C1 c f) where
  genericConstrName x = conName x
-- --------------------------------------------------


pDominators 
  :: Maybe Int 
  -- ^ How deep should we recurse?
  -> Debuggee 
  -> IO ()
pDominators lim e = do
  pause e
  runTrace e $ do
    _bs <- precacheBlocks
    roots <- gcRoots
    liftIO $ hPutStrLn stderr "!!!!! Done gcRoots !!!!!"

    ns0 <- liftIO getMonotonicTime
    hg :: HeapGraph Size <- case roots of
      [] -> error "Empty roots"
      (x:xs) -> do
        multiBuildHeapGraph lim (x :| xs)
    ns1 <- liftIO getMonotonicTime
    liftIO $ hPutStrLn stderr $ "!!!!! Done multiBuildHeapGraph !!!!! in "<>(show $ (ns1-ns0))

    -- Validate that sizes in dominator tree seem right:
    let !sizeTot = IM.foldl' (\s e_-> s + hgeData e_) 0 $ graph hg
    liftIO $ hPutStrLn stderr $ "!!!!! Total size: "<> (show sizeTot)

  {-
    -- Further try to validate that heap sizes seem right...
    liftIO $ putStrLn "!!!!!! ----------------- !!!!!!!"
    liftIO $ summariseBlocks _bs
    liftIO $ putStrLn "!!!!!! ----------------- !!!!!!!"
    mblockMap <- censusByMBlock (map hgeClosurePtr $ IM.elems $ graph hg)
    liftIO . print $ length mblockMap
    liftIO . print $ ("totsize", sum $ fmap cssize mblockMap)
    liftIO $ putStrLn "!!!!!! ----------------- !!!!!!!"
    error "DONE!"
  -}
    
    forrest <- forM (retainerSize hg) $ \tree -> do
      -- get some pieces we're interested in:
      let fiddle hge =
            let (Size s, RetainerSize rs) = hgeData hge
                i = info $ hgeClosure hge
                t = tipe $ decodedTable i
             -- (size of this and all children, size of just us, closure type, InfoTablePtr)
             in ((rs, s, t), tableId i)
      pure (fiddle <$> tree)
      
    -- recursively sort tree so largest retained sizes at top:
    let sortTree (Node x xs) = Node x $ sortBy (flip compare `on` rootLabel) $ map sortTree xs
        
    -- For validating whether we've got close to the heap size we expect represented 
    let totalRetained = sum $ map (\(Node ((rs,_,_),_) _)-> rs) forrest
        totalRetainedMB :: Float
        totalRetainedMB = fromIntegral totalRetained / 1_000_000
    liftIO $ hPutStrLn stderr $ "!!! TOTAL SIZE RETAINED REPORTED: "<> show totalRetainedMB <> " MB"

    -- Sort just top-level
    let forrestSorted = sortBy (flip compare `on` rootLabel) forrest
  {- TODO what was the goal here?
    -- descend until we're at 90% of peak
    let limFactor = 0.2
    let rLimLower = case forrestSorted of
          (Node ((rBiggest,_,_),_) _ : _) -> round (fromIntegral rBiggest * limFactor)
          _ -> error "Blah"
    liftIO $ hPutStrLn stderr $ show ("rLimLower", rLimLower)

    let goDescend n@(Node ((rSize, x, y), ptr) ns)
          | rSize > rLimLower =  F.for_ ns goDescend
          | otherwise = do
              nAnnotated <- forM n $ traverse getSourceInfo
              liftIO $ putStrLn $ drawTree $ fmap show nAnnotated
                
    F.for_ forrestSorted $ goDescend . sortTree
    -}
    
  -- {-
    let tree0 =
          Node ((0,0,TSO), nullInfoTablePtr) $ --nonsense
            forrestSorted

    -- let tree1 = topThunkClosures tree0
    let tree1 = pruneDownToPct 0.001 tree0

    -- Annotate all with source info
    tree2 <- forM tree1 $ traverse $ \tid -> 
      if tid == nullInfoTablePtr -- dumb workaround for root of tree...
         then return Nothing
         else getSourceInfo tid

    liftIO $ putStrLn $ drawTree $
      fmap show $ sortTree tree2
      -- -}


    -- {-
-- Prune all grandchildren of thunks, for clarity/brevity:
topThunkClosures :: Tree ((x, y, ClosureType), InfoTablePtr) -> Tree ((x, y, ClosureType), InfoTablePtr)
topThunkClosures (Node n@((_, _, tp), _) forrest)
  | tp `elem` [ THUNK , THUNK_1_0 , THUNK_0_1 , THUNK_2_0 , THUNK_1_1 , THUNK_0_2 , THUNK_STATIC , THUNK_SELECTOR]
      = Node n $ map prune forrest  -- remove grandchildren
  | otherwise = Node n $ map topThunkClosures forrest
  where prune (Node x _) = Node x []

-- ...or alternatively, prune children with retained size under some magnitude:
-- assumes reverse sorted tree by retained
pruneDownToPct :: Float -> Tree ((Int, y, ClosureType), InfoTablePtr) -> Tree ((Int, y, ClosureType), InfoTablePtr)
pruneDownToPct p _root@(Node x forrest) = Node x $ mapMaybe go forrest
  where limLower = case forrest of
          (Node ((rBiggest,_,_),_) _ : _) -> round (fromIntegral rBiggest * p)
          _ -> error "Blah"
        
        go (Node n@((r,_,_),_) ns)
          | r < limLower = Nothing
          | otherwise = Just $ Node n $ mapMaybe go ns

  -- -}

defaultSnapshotLocation :: String
defaultSnapshotLocation = "/tmp/ghc-debug-cache"

-- Take snapshots in a loop forever, at intervals, overwriting.
pSteppingSnapshot :: Debuggee -> IO ()
pSteppingSnapshot e = forM_ [(0::Int)..] $ \i -> do
  makeSnapshot e defaultSnapshotLocation
  putStrLn ("CACHED: " ++ show i)
  threadDelay 5_000_000

-- TODO add to ghc-debug?
nullInfoTablePtr :: InfoTablePtr
nullInfoTablePtr = InfoTablePtr 0


-- TODO add to ghc-debug
emptyTraceFunctions :: (MonadTrans m, Monad (m DebugM))=> TraceFunctions m
emptyTraceFunctions =
  TraceFunctions {
       papTrace = const (lift $ return ())
     , stackTrace = const (lift $ return ())
     , closTrace = \_ _ -> id -- ^ Just recurse
     , visitedVal = const (lift $ return ())
     , conDescTrace = const (lift $ return ())
   }

-- TODO add to ghc-debug
deriving instance MonadIO DebugM

getSourceLoc :: DebugClosureWithSize pap string s b -> DebugM (Maybe SourceInformation) 
getSourceLoc c = getSourceInfo (tableId (info (noSize c)))

-- ================================================================================

-- TODO ...then a mode that consumes size of child without source info (add a bool flag)
-- TODO dominator tree with accumulating sizes...
--    TODO incorporate fgl (for above), 
--         add a simple repl for doing queries, displaying data
-- TODO print stats, e.g. objects by module

data ClusteringStrategy 
    = ClusterByInfoTable -- ^ node per info-table, with accumulated size in bytes
    | ClusterBySourceInfo Bool 
    -- ^ above but go further, folding nodes with identical (but not missing)
    -- metadata. 'True' here indicates whether to go further and cluster on
    -- source location spans, ignoring type information (type will be labeled
    -- "VARIOUS")
    deriving (Show, Read, Eq)

-- | Write out the heap graph to a file, in GML format
-- ( https://web.archive.org/web/20190303094704/http://www.fim.uni-passau.de:80/fileadmin/files/lehrstuhl/brandenburg/projekte/gml/gml-technical-report.pdf )
--
-- directed edge means "retains", with weights counting number of such relationships
pClusteredHeapGML :: ClusteringStrategy -> FilePath -> Debuggee -> IO ()
pClusteredHeapGML clusteringStrategy path e = do
  pause e
  runTrace e $ do
    _bs <- precacheBlocks
    liftIO $ hPutStrLn stderr "!!!!! Done precacheBlocks !!!!!"
    roots <- gcRoots
    liftIO $ hPutStrLn stderr "!!!!! Done gcRoots !!!!!"

    outHandle <- unsafeLiftIO $ openFile path WriteMode

    when (dropWhile (/='.') path /= ".gml") $
       error "Only .gml supported"

    -- GML only supports Int32 Ids, so we need to remap iptr below
    (nodes, edges, _) <- flip execStateT (mempty, mempty, 1::Int32) $ 
       -- 'traceFromM' visits every closure once, accounting for cycles
       traceFromM emptyTraceFunctions{closTrace = closTraceFunc} roots

    unsafeLiftIO $ do
      hPutStrLn stderr "!!!!! Start writing to file !!!!!"
      writeToFile nodes edges outHandle
      hPutStrLn stderr $ "!!!!! Done writing "<>path<> " !!!!!"
      hClose outHandle

  where
    writeToFile 
      :: Map.Map InfoTablePtr ((Maybe SourceInformation, String, Bool, Int32), Size) 
      -> Map.Map (InfoTablePtr, InfoTablePtr) Int
      -> Handle
      -> IO ()
    writeToFile nodes edges outHandle = do
      -- TODO factor this out; monadic just to control scope
      (edgesToWrite, nodesToWrite) <- case clusteringStrategy of
            -- --------
            ClusterByInfoTable -> pure $
              -- just 'nodes' and 'edges', with no meaningful modifications:
              let nodesToWrite = map (\(x, size) -> (x, size, [])) $ Map.elems nodes -- []: no folded infoTable nodes
                  edgesToWrite = map (\((ptrFrom, ptrTo), cnt) -> (toPtr32 ptrFrom, toPtr32 ptrTo, cnt)) $ Map.toList edges 
                      where toPtr32 ptr = (\((_, _, _, iptr32), _)-> iptr32) $ fromJust $ Map.lookup ptr nodes
               in (edgesToWrite, nodesToWrite)
            -- --------
            ClusterBySourceInfo justBySourceLoc -> pure $
              -- we'll write nodesNoInfo out unmodified, and fold identical nodesByInfo_dupes:
              let (nodesNoInfo, nodesByInfo_dupes) = partitionEithers $ map (uncurry hasSourceInfo) $ Map.toList nodes
                    where
                      hasSourceInfo iptr (xMeta@(mbSI, x, y, z), size) = case mbSI of
                          Just si@SourceInformation{..} 
                            -- We'll fold nodes with a key like e.g.: 
                            -- ("main.balancedTree","example/Main.hs:25:67-69","Tree")
                            -- ...so long as we have defined code location
                            | all (not . null) [infoLabel, infoPosition]
                                -> Right $ if justBySourceLoc
                                              then (infoPosition                          
                                                   , ((Just si{infoLabel="VARIOUS", infoType="VARIOUS"},x,y,z), size, [iptr]))
                                              else (infoLabel <> infoPosition <> infoType 
                                                   , (xMeta, size, [iptr]))
                          _     -> Left (xMeta, size, []) -- []: no folded infoTable nodes
                  
                  nodesByInfo :: Map.Map String -- either (infoLabel <> infoPosition <> infoType) or just infoPosition, if justBySourceLoc
                                         ((Maybe SourceInformation, String, Bool, Int32), Size, [InfoTablePtr]) 
                  nodesByInfo = Map.fromListWith mergeNodes nodesByInfo_dupes
                    -- merge sizes in bytes, store source infotable ptrs so we can
                    -- remap edges and store as graph metadata the number of folded nodes:
                    where mergeNodes ( ( mbSI0,  closureTypeStr0,  isThunk0, iptr32_0), size0, iptrs0 )
                                     ( (_mbSI1, _closureTypeStr1, _isThunk1, iptr32_1), size1, iptrs1 ) =
                                         -- NOTE: keep the smallest iptr32, since that corresponds to first seen in traversal:
                                       ( (mbSI0, closureTypeStr0, isThunk0, min iptr32_0 iptr32_1), size0+size1 , iptrs1<>iptrs0 )

                  -- map edge src/dst ids to the new folded node ids, combine counts of any now-folded edges
                  edgesRemapped :: Map.Map (Int32, Int32) Int
                  edgesRemapped  = Map.fromListWith (+) $ map (first (remap *** remap)) $ Map.toList edges where
                    remap iptr = fromMaybe iptr32Orig $ Map.lookup iptr iptrRemapping where
                      -- this to/from node couldn't be folded (since no source info,
                      -- probably), so use the original node's int32 key
                      !iptr32Orig = case Map.lookup iptr nodes of
                                      Nothing -> error "Impossible! edgesRemapped"
                                      Just ((_, _, _, iptr32), _) -> iptr32

                    iptrRemapping :: Map.Map InfoTablePtr Int32
                    iptrRemapping = Map.fromList $ concatMap iptrsToIptrs32 $ Map.elems nodesByInfo where
                      iptrsToIptrs32 ((_, _, _, iptr32), _, iptrs) = map (,iptr32) iptrs

                  -- output:
                  nodesToWrite = Map.elems nodesByInfo <> nodesNoInfo
                  edgesToWrite = map (\((ptrFrom, ptrTo), cnt) -> (ptrFrom, ptrTo, cnt)) $ Map.toList edgesRemapped

               in (edgesToWrite, nodesToWrite)

      -- ------------------------ write gml file
      writeOpenGML

      F.for_ nodesToWrite $ \((mbSI, closureTypeStr, isThunk, iptr32), size, iptrsFolded) -> 
        writeNode (length iptrsFolded) iptr32 isThunk size $
          case mbSI of
            Nothing ->
              (closureTypeStr, Nothing)
            Just SourceInformation{..} ->
              (closureTypeStr<>" "<>infoType, Just (infoLabel, infoPosition))

      F.for_ edgesToWrite writeEdge
      writeCloseGML
      where
        write = hPutStr outHandle

        ---- GML File format:
        writeOpenGML =
          write $ "graph [\n"
               <> "comment \"this is a graph in GML format\"\n"
               <> "directed 1\n"
        writeCloseGML =
          write $ "]\n"

        writeEdge (iptrFrom32, iptrTo32, cnt) = do
          write $  "edge [\n"
                <> "source "<> show iptrFrom32 <> "\n"
                <> "target "<> show iptrTo32   <> "\n"
                <> "count "<> show cnt         <> "\n"
                <> "]\n"

        writeNode 
            :: Int
            -- ^ number of folded per-info-table clusters here;  these would
            -- expand into n+1 nodes under ClusterByInfoTable
            -> Int32 
            -> Bool -> Size -> (String , Maybe (String,String)) -> IO ()
        writeNode iptrsFoldedCnt iptr32 isThunk size (typeStr,mbMeta) = do
          -- The spec is vague, but graphia chokes on \" so strip:
          let renderQuoted = show . filter (/= '"')
          write $ "node [\n"
                <> "id " <> show iptr32 <> "\n"
                <> (guard isThunk >> 
                   "isThunk 1\n")
                <> "sizeBytes " <> show (getSize size) <> "\n"
                <> "infotablesFoldedCnt " <> show iptrsFoldedCnt <> "\n"
                -- string attributes; need to be quoted:
                <> "type " <> renderQuoted typeStr <> "\n"
                <> (case mbMeta of 
                      Nothing -> ""
                      Just (infoLabel, infoPosition) ->
                           "name "<> renderQuoted infoLabel<> "\n"
                        <> "pos " <> renderQuoted infoPosition<> "\n"
                   )
                <> "]\n"

    closTraceFunc _ptr (DCS size clos) continue = do
      (nodes, edges, iptr32) <- get
      let tid@(InfoTablePtr _iptr) = tableId $ info clos

      (!nodes', !iptr32') <-
        if Map.member tid nodes
          -- Just accumulate the size from this new node:
          -- TODO add counts
          then pure (Map.adjust (fmap (+size)) tid nodes  , iptr32)
          -- Use iptr32 and increment for the next new node
          else lift $ do
            -- 'tipe' also ends up in SourceInformation, but not all info tables have that
            let closureTypeStr = show $ tipe $ decodedTable $ info clos
            let isThunk = "THUNK" `isPrefixOf` closureTypeStr
            getSourceInfo tid >>= \case
              -- TODO in what cases is source info not present?
              Nothing -> 
                pure (Map.insert tid ((Nothing, closureTypeStr, False, iptr32), size) nodes, iptr32+1)
              Just si@SourceInformation{} -> do
                -- When we record edges, we'll record some special metadata when from isThunk
                pure (Map.insert tid ((Just si, closureTypeStr, isThunk, iptr32), size) nodes, iptr32+1)

      -- Collect all outgoing edges from this closure...
      !edges' <- lift $ flip execStateT edges $
          -- Here we go one hop further to build (possibly to an already-visited 
          -- node which we wouldn't be able to reach via traceFromM)
          -- TODO this is probably slow, since we need to resolve the InfoTablePtr again to make an edge
          void $ flip (quadtraverse pure pure pure) clos $ \toPtr-> do
            (DCS _ toClos) <- lift $ dereferenceClosure toPtr
            let tidTarget = tableId $ info toClos
            -- Increase edge count tid -> tidTo by one, else add new edge
            modify $ Map.insertWith (+) (tid, tidTarget) 1

      put (nodes', edges', iptr32')
      
      continue
