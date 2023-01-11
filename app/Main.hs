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
import qualified Data.IntMap.Strict as IM
-- import Data.Bitraversable
-- import Data.Monoid
-- import Control.Applicative
-- import Data.Traversable
import Data.Kind
import Data.Tuple
import Data.Word

-- import System.Process
import System.Environment
import System.IO
import Data.Tree
import Data.Maybe
import Data.Either
import Control.Arrow (first, (***), (&&&))
import qualified Data.Map.Strict as Map
import qualified Data.Map.Lazy as LazyMap
-- import Data.Ord
import Data.List
import Data.Function
import Data.List.NonEmpty(NonEmpty(..))
-- import Data.Function
import GHC.Generics
import GHC.Clock

import GHC.Int

import qualified Data.Graph.Inductive.Graph as FGL
import qualified Data.Graph.Inductive.PatriciaTree as FGL
import qualified Data.Graph.Inductive.Query.Dominators as FGL
import qualified Data.Set as Set


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
         -- pClusteredHeapGML (ClusterBySourceInfo False) "/tmp/per-infoTable-byLoc-NEW"
         pAnalyzePointerCompression
         -- pAnalyzeNestedClosureFreeVars
         -- pInfoTableTree
         -- pDistinctInfoTableAnalysis
         -- pCommonPtrArgs
         -- pPointersToPointers

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
          cs' <- mapM (quintraverse pure pure dereferenceConDesc pure pure) cs
          locs <- mapM getSourceLoc cs'
          -- displayRetainerStack is arbitrary and weird...
          -- TODO could be cool to look for the last thunk in the list (highest up in retainer tree)
          -- TODO would be cool to call out the top-most line from our own codebase too
          liftIO $ putStrLn "FIXME for 0.4!"
          -- liftIO $ displayRetainerStack 
          --   [ ("", zip cs' locs) ]

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
          void $ quintraverse pure pure pure pure sendEdge clos
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

-- See also pClusteredHeapGML which annotates dominator size, clustered by infotable/source loc
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
     , srtTrace = const (lift $ return ())
     , stackTrace = const (lift $ return ())
     , closTrace = \_ _ -> id -- ^ Just recurse
     , visitedVal = const (lift $ return ())
     , conDescTrace = const (lift $ return ())
   }

-- TODO add to ghc-debug
deriving instance MonadIO DebugM

getSourceLoc :: DebugClosureWithSize srt pap string s b -> DebugM (Maybe SourceInformation) 
getSourceLoc c = getSourceInfo (tableId (info (noSize c)))

-- ================================================================================

-- TODO ...then a mode that consumes size of child without source info (add a bool flag)
-- TODO add a simple repl for doing queries, displaying data
-- TODO print stats, e.g. objects by module

data ClusteringStrategy 
    = ClusterByInfoTable -- ^ node per info-table, with accumulated size in bytes
    | ClusterBySourceInfo Bool 
    -- ^ above but go further, folding nodes with identical (but not missing)
    -- metadata. 'True' here indicates whether to go even further and cluster on
    -- source location spans, ignoring type information (type will be labeled
    -- "VARIOUS")
    deriving (Show, Read, Eq)

-- | Write out the heap graph, with heap objects clustered by info table, to a
-- file, in GML format:
--
--    https://web.archive.org/web/20190303094704/http://www.fim.uni-passau.de:80/fileadmin/files/lehrstuhl/brandenburg/projekte/gml/gml-technical-report.pdf 
--
-- Directed edge in the normal graph means "retains", with weights counting
-- number of such relationships; in the dominator tree graph an edge means
-- "only reachable by".
--
-- Both graphs have nodes tagged with size and transitive dominated size (i.e.
-- size of self and all dominated child nodes)
pClusteredHeapGML :: ClusteringStrategy -> FilePath -> Debuggee -> IO ()
pClusteredHeapGML clusteringStrategy pathNoExtension e = do
  pause e
  runTrace e $ do
    _bs <- precacheBlocks
    liftIO $ hPutStrLn stderr "!!!!! Done precacheBlocks !!!!!"
    roots <- gcRoots
    liftIO $ hPutStrLn stderr "!!!!! Done gcRoots !!!!!"

    -- GML only supports Int32 Ids, so we need to remap iptr below
    -- NOTE: addDominatedSize assumes 1 is the root node
    (nodes, edges, _) <- flip execStateT (mempty, mempty, 1::Int32) $ 
       -- 'traceFromM' visits every closure once, accounting for cycles
       traceFromM emptyTraceFunctions{closTrace = closTraceFunc} roots

    let (edgesToWrite, nodesClustered) = buildClusteredGraph nodes edges clusteringStrategy

    -- add transitive dominated size to nodes:
    let (nodesToWriteMap, dominatedEdges) = addDominatedSize nodesClustered edgesToWrite
        nodesToWrite = Map.elems nodesToWriteMap

    unsafeLiftIO $ do
      hPutStrLn stderr "!!!!! Start writing to file !!!!!"

      let path = pathNoExtension<>".gml"
      outHandle <- openFile path WriteMode
      writeToFile nodesToWrite edgesToWrite outHandle
      hClose outHandle
      hPutStrLn stderr $ "!!!!! Done writing regular graph at "<>path<> " !!!!!"

      -- Write out a separate dominator tree graph (we'd really prefer if
      -- graphia could just do this transform):
      let domTreePath = pathNoExtension<>".dominator_tree.gml"
      outHandleDomTree <- openFile domTreePath WriteMode
      writeToFile nodesToWrite dominatedEdges outHandleDomTree
      hClose outHandleDomTree
      hPutStrLn stderr $ "!!!!! Done writing dominator tree graph at "<>domTreePath<> " !!!!!"

  where
    writeToFile
      :: [((Maybe SourceInformation, String, Bool, Int32), Size, Size, [a])]
      -> [(Int32, Int32, Int)] 
      -> Handle 
      -> IO ()
    writeToFile nodesToWrite edgesToWrite outHandle = do
      writeOpenGML

      F.for_ nodesToWrite $ \((mbSI, closureTypeStr, isThunk, iptr32), size, sizeDominated, iptrsFolded) -> 
        writeNode (length iptrsFolded) iptr32 isThunk size sizeDominated $
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
            -> Bool -> Size -> Size -> (String , Maybe (String,String)) -> IO ()
        writeNode iptrsFoldedCnt iptr32 isThunk size sizeDominated (typeStr,mbMeta) = do
          -- The spec is vague, but graphia chokes on \" so strip:
          let renderQuoted = show . filter (/= '"')
          write $ "node [\n"
                <> "id " <> show iptr32 <> "\n"
                <> (guard isThunk >> 
                   "isThunk 1\n")
                <> "sizeBytes " <> show (getSize size) <> "\n"
                <> "sizeTransitiveDominated " <> show (getSize sizeDominated) <> "\n"
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
      -- TODO is info pointer included in `size`? It seems only STATIC closures have just 8 bytes
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
          void $ flip (quintraverse pure pure pure pure) clos $ \toPtr-> do
            (DCS _ toClos) <- lift $ dereferenceClosure toPtr
            let tidTarget = tableId $ info toClos
            -- Increase edge count tid -> tidTo by one, else add new edge
            modify $ Map.insertWith (+) (tid, tidTarget) 1

      put (nodes', edges', iptr32')
      
      continue

buildClusteredGraph 
  :: Map.Map InfoTablePtr ((Maybe SourceInformation, String, Bool, Int32), Size)
  -> Map.Map (InfoTablePtr, InfoTablePtr) Int
  -> ClusteringStrategy
  -> ([(Int32, Int32, Int)],
      Map.Map Int32 ((Maybe SourceInformation, String, Bool, Int32), Size, [InfoTablePtr])
     )
buildClusteredGraph nodes edges = \case
  -- --------
  ClusterByInfoTable ->
    -- just 'nodes' and 'edges', with no meaningful modifications:
    let nodesToWrite = Map.fromList $ 
                         map (\t@(x, size) -> (getIptr32 t, (x, size, []))) $  -- []: no folded infoTable nodes
                         Map.elems nodes
        edgesToWrite = map (\((ptrFrom, ptrTo), cnt) -> (toPtr32 ptrFrom, toPtr32 ptrTo, cnt)) $ Map.toList edges 
            where toPtr32 ptr = getIptr32 $ fromJust $ Map.lookup ptr nodes
     in (edgesToWrite, nodesToWrite)
  -- --------
  ClusterBySourceInfo justBySourceLoc ->
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
                             ( (mbSI0, closureTypeStr0, isThunk0, min iptr32_0 iptr32_1) 
                                 -- merge sizes:
                                 , size0+size1 , iptrs1<>iptrs0 )

        -- map edge src/dst ids to the new folded node ids, combine counts of any now-folded edges
        edgesRemapped :: Map.Map (Int32, Int32) Int
        edgesRemapped  = Map.fromListWith (+) $ map (first (remap *** remap)) $ Map.toList edges where
          remap iptr = fromMaybe iptr32Orig $ Map.lookup iptr iptrRemapping where
            -- this to/from node couldn't be folded (since no source info,
            -- probably), so use the original node's int32 key
            !iptr32Orig = maybe (error "Impossible! edgesRemapped") getIptr32 $ Map.lookup iptr nodes

          iptrRemapping :: Map.Map InfoTablePtr Int32
          iptrRemapping = Map.fromList $ concatMap iptrsToIptrs32 $ Map.elems nodesByInfo where
            iptrsToIptrs32 ((_, _, _, iptr32), _, iptrs) = map (,iptr32) iptrs

        -- output:
        nodesClustered = Map.fromList $ map (getIptr32_ &&& id) $
                          Map.elems nodesByInfo <> nodesNoInfo
        edgesToWrite = map (\((ptrFrom, ptrTo), cnt) -> (ptrFrom, ptrTo, cnt)) $ Map.toList edgesRemapped

     in (edgesToWrite, nodesClustered)
  where getIptr32 ((_, _, _, iptr32), _) = iptr32
        getIptr32_ ((_, _, _, iptr32), _,_) = iptr32

-- Generate a dominator tree from the graph, annotating each node with the
-- transitive size of the graph it dominates; i.e. the total size in bytes of
-- all its descendents.
addDominatedSize ::
    Map.Map Int32 ((a, b, c, Int32), Size, ds) -> 
    [(Int32, Int32, int)] ->
      ( Map.Map Int32 ((a, b, c, Int32), Size, Size, ds)
      , [(Int32, Int32, Int)])
      -- ^ Also return immediately-dominates relationship edges (with 0 weight)
addDominatedSize nodes0 edges =
      -- NOTE: iDom returns reverse order from dominator tree edges:
  let dominatesEdges = map swap $ FGL.iDom g 1

      -- lazily accumulate transitive dominator sub-tree sizes
      -- leaves will be missing, but their sizes accounted for
      transSizes = 
          let domNodesChilds :: LazyMap.Map Int [Int] 
              domNodesChilds = LazyMap.fromListWith (<>) $ map (fmap pure) dominatesEdges
           in LazyMap.mapWithKey accum domNodesChilds
          where accum parent children = sizeOf parent + (sum $ map transSizeOf children)

      transSizeOf nodeId = 
        fromMaybe (sizeOf nodeId) $ -- ...if it's a leaf of dominator tree
          LazyMap.lookup nodeId transSizes

      annotate xsz@(x, sz, ds) = (x, sz, transSizeOf $ getNodeId xsz, ds)

      -- back to our Int32 keys; just put 0 for edge weight, arbitrarily::
      dominatesEdges32 = map (\(src, dest) -> (fromIntegral src, fromIntegral dest, 0)) dominatesEdges

   in (fmap annotate nodes0, dominatesEdges32)
   where
      getKey i = getNodeId $ fromJust $ Map.lookup i nodes0
      getNodeId ((_, _, _, iptr32), _, _) = fromIntegral iptr32

      g :: FGL.Gr Size ()
      g = FGL.mkGraph fglNodes fglEdges
      fglNodes = map (getNodeId &&& \(_, sz, _)-> sz) $ Map.elems nodes0
      -- drops edge weights entirely
      fglEdges = map ( \(fromI,toI,_)-> (getKey fromI, getKey toI, ()) ) edges

      sizeOf = fromJust . FGL.lab g

test_addDominatedSize :: Bool
test_addDominatedSize = 
    -- From https://en.wikipedia.org/wiki/Dominator_(graph_theory)
    let edges = map (\(f,t)-> (f,t,()))  [(1,2), (2, 3), (2, 4), (2, 6), (3, 5), (4, 5), (5, 2)]
        -- make the size equal to node id
        nodes = Map.fromList $ map (\n-> (n,  (((),(),(),fromIntegral n), fromIntegral n, ())  )) [1..6]

        expected =
            Map.fromList [
                (1,(((),(),(),1),Size {getSize = 1},Size {getSize = 21},())),
                -- own size (2) + 3+4+5+6 = 20:
                (2,(((),(),(),2),Size {getSize = 2},Size {getSize = 20},())),
                -- leaves just accum their own size:
                (3,(((),(),(),3),Size {getSize = 3},Size {getSize = 3},())),
                (4,(((),(),(),4),Size {getSize = 4},Size {getSize = 4},())),
                (5,(((),(),(),5),Size {getSize = 5},Size {getSize = 5},())),
                (6,(((),(),(),6),Size {getSize = 6},Size {getSize = 6},()))]

     in expected == fst (addDominatedSize nodes edges)

-- ================================================================================

-- | A value of N means: this pointer needs at least N bits (plus a sign bit)
-- if represented as an /offset/ from the closure header (or from the first
-- child pointer, as in histSiblingOffs)
type BitWidthBucket = Int

data AnalyzePointerCompressionStats = AnalyzePointerCompressionStats {
       infoTableMin :: Word64
     , infoTableMax :: Word64
     , infoPointers :: Map.Map Word64 Int
     , lastPointingNext :: Int
     -- ^ number of last-in-object pointers pointing to next adjacent heap object
     , histFirst :: Map.Map BitWidthBucket Int
     , histLast :: Map.Map BitWidthBucket Int
      -- ^ stats on the first and last heap pointers of a closure
     , histOffs :: Map.Map (BitWidthBucket, Int) Int
      -- ^ histogram of heap pointers on an individual basis, bucketed by offset
      -- distance and number of sibling pointers:
     , histSiblingOffs :: Map.Map (BitWidthBucket, Int) Int
     -- ^ (like above, but offset from the first sibling pointer value)
     , histMaxOffs :: Map.Map (BitWidthBucket, Int) Int
      -- ^ ...whereas if all child pointers of a closure had to be equal sized
      -- signed ints, what size would we need for all the pointers in this
      -- closure? (these will all be positive bit width buckets):
     , blockGraph :: IM.IntMap (Map.Map Int Int)
      -- ^ a graph from block to block, where we make an edge if any heap
      -- pointer in the source block points to the destination block. Mark the
      -- edge with a count. Limit edges to maxBlockGraphEdgesToRecord (i.e.
      -- `Map int Int` of size maxBlockGraphEdgesToRecord means,
      -- "maxBlockGraphEdgesToRecord or more"). Includes self edges
     , histClosureSizes :: Map.Map Int Int
      -- ^ size in bytes -> total size in bytes for all closures of this size
      --
      -- The largest bucket means "N and larger"
     } deriving (Show, Eq)

emptyAnalyzePointerCompressionStats :: AnalyzePointerCompressionStats
emptyAnalyzePointerCompressionStats =
    AnalyzePointerCompressionStats maxBound minBound mempty 0 mempty mempty mempty mempty mempty mempty mempty

-- What are the prospective benefits of pointer compression on this heap?
pAnalyzePointerCompression :: Debuggee -> IO ()
pAnalyzePointerCompression e = do
  pause e
  runTrace e $ do
    _bs <- precacheBlocks
    liftIO $ hPutStrLn stderr "!!!!! Done precacheBlocks !!!!!"
    roots <- gcRoots
    liftIO $ hPutStrLn stderr "!!!!! Done gcRoots !!!!!"

    -- Use state to collect:
    --   - range of info tables
    --   - histograms of offsets of first and last pointer field in closure (if any)
    --   - histogram of offsets for every field
    --   - histogram of `maximum offsets`, where 'offsets' are all the pointer fields in a closure
    --   ...the latter two also keyed by number of child pointers, up to 6+
    AnalyzePointerCompressionStats{..} 
       <- flip execStateT emptyAnalyzePointerCompressionStats $
            traceFromM emptyTraceFunctions{closTrace = closTraceFunc} roots

    -- --------- Output and analysis:
    liftIO $ do
        putStrLn "========= Raw output ======================================"
        -- print infoPointers   -- < lots of output
        putStrLn "* offset bits buckets for first and last pointers:"
        print histFirst
        print histLast
        putStrLn "* count of final heap pointers pointing to adjacent heap object to the right:"
        print lastPointingNext
        putStrLn "* count of heap pointers by (offset bits bucket, pointers in closure):"
        print histOffs
        putStrLn "* (NEW!) count of sibling heap pointers by (offset-from-first-sibling-pointer-val bits bucket, pointers in closure):"
        print histSiblingOffs
        putStrLn "* count of closures by (offset bits reqd. for all fields, pointers in closure):"
        print histMaxOffs
        putStrLn "* (NEW!) histogram of heap residency, by closure size (divide to get counts)"
        print histClosureSizes

        putStrLn "========= Analysis   ======================================"
        let infoTableRange :: Double
            infoTableRange = fromIntegral $ infoTableMax - infoTableMin
        putStrLn $ "infotables + code range, in bits: "<> (show $ logBase 2 infoTableRange)

        putStrLn "----------------------------------"
        let (pos,neg) = (f *** f) $ partition ((>0) . fst . fst) $ Map.toList histOffs
              where f = sum . map snd
        putStrLn $ "Percentage of pointers representable as positive offset: " 
                <>show (pct pos (pos+neg))

        putStrLn "----------------------------------"
        let pointersByObjectSizeMembership =
              Map.fromListWith (+) $ map (first snd) $ Map.toList histOffs
            totalPointersCnt = sum pointersByObjectSizeMembership
        putStrLn $ "Out of "<>show totalPointersCnt<>" total heap pointers..."
        F.for_ (Map.toList pointersByObjectSizeMembership) $ \(ptrFields, cnt) -> do
            let end | ptrFields == 6 = " 6 or more sibling pointers"
                    | otherwise = " "<>show ptrFields<>" sibling pointers"
            putStrLn $ "  ..."<>show (pct cnt totalPointersCnt)<>"% of heap pointers are in objects with"<>end

        putStrLn "----------------------------------"
        let closuresByObjectSize =
              Map.fromListWith (+) $ map (first snd) $ Map.toList histMaxOffs
            totalClosCount = sum closuresByObjectSize
        putStrLn $ "Out of "<>show totalClosCount<>" total closures..."
        F.for_ (Map.toList closuresByObjectSize) $ \(ptrFields, cnt) -> do
            let end | ptrFields == 6 = " 6 or pointer fields"
                    | otherwise = " "<>show ptrFields<>" pointer fields"
            putStrLn $ "  ..."<>show (pct cnt totalClosCount)<>"% have"<>end

        putStrLn "----------------------------------"
        -- we'll assume 6 or more to be exactly six
        -- (here and elsewhere assume x86_64)
        putStrLn "Conservative estimate of size of heap pointers + info pointers:"
        let totalPtrBytes = 
                -- 1 Word for info pointer 1 word for each ptr field
                foldl' (\n (ptrFields,cnt)-> n + ((8*cnt)*(1 + ptrFields))) 0 $ 
                  Map.toList closuresByObjectSize
        putStrLn $ "   "<>show (totalPtrBytes `div` (1000*1000))<>" MB"

        putStrLn "----------------------------------"
        putStrLn "If all heap pointers in an object must have same width compressed (i.e. as offset),"
        let closuresByOffsetBits =
              Map.fromListWith (+) $ map (first fst) $ Map.toList histMaxOffs
        F.for_ (Map.toList closuresByOffsetBits) $ \(bitWidth, cnt) -> do
            putStrLn $ "  ... "<>show (pct cnt totalClosCount)<> "% of closures could use offsets of width "
             <>show (min 64 (bitWidth+2)) -- make these normal word sizes

        putStrLn "----------------------------------"
        let numBlocks = IM.size blockGraph
            blockEdges = Map.fromListWith (+) $ 
                map (\(_blk, outEdges) -> (Map.size outEdges, 1::Int)) $ IM.toList blockGraph
        putStrLn $ "Out of "<>show numBlocks<>" blocks..."
        F.for_ (Map.toList blockEdges) $ \(numOutEdges, countOfSuchBlocks) -> do
          if numOutEdges == maxBlockGraphEdgesToRecord
             then
                putStrLn $ "    ... "<>show (pct countOfSuchBlocks numBlocks)<>"% have edges to "
                         <>show numOutEdges<>" or more other blocks"
             else
                putStrLn $ "    ... "<>show (pct countOfSuchBlocks numBlocks)<>"% have edges to exactly "
                         <>show numOutEdges<>" distinct other blocks"

  where
    pct :: Integral n=> n -> n -> Int
    pct num den = round ((fromIntegral num / fromIntegral den)*100::Float)

    -- so we don't blow up memory
    maxBlockGraphEdgesToRecord = 20

    closTraceFunc cp@(UntaggedClosurePtr ptr) (DCS (Size size) clos) continue = do
      AnalyzePointerCompressionStats{..} <- get
      let (InfoTablePtr iptr) = tableId $ info clos
          !infoTableMax' = max infoTableMax iptr
          !infoTableMin' = min infoTableMin iptr
          -- just collect all info pointers, to see what's really going on:
          -- (expect most counts to be 1 due to distinct-info-tables):
          !infoPointers' = Map.insertWith (+) iptr 1 infoPointers

      toPtrs <- fmap reverse $ lift $ flip execStateT [] $
          -- Here we go one hop further to get this closure's pointers
          void $ flip (quintraverse pure pure pure pure) clos $ \(UntaggedClosurePtr toPtr)-> do
              ptrStack <- get
              put (toPtr:ptrStack)

      -- the last bucket indicates "six or more pointers"
      let !numFieldsBucket = min 6 $ length toPtrs

      -- stats on the first and last heap pointers of a closure
      let goHistFirstLast mp = \case
              [] -> histFirst
              (toPtr:_) ->
                let bucket = offsetFromPtrBucket toPtr
                 in Map.insertWith (+) bucket 1 mp 
      let !histFirst' = goHistFirstLast histFirst toPtrs
      let !histLast' = goHistFirstLast histLast $ reverse toPtrs

      -- histogram of heap pointers on an individual basis, bucketed by offset
      -- distance and number of sibling pointers:
      let !histOffs' = foldl' (flip go) histOffs toPtrs where
            go toPtr = Map.insertWith (+) bucket 1 where
              bucket = (offsetFromPtrBucket toPtr, numFieldsBucket)

     -- TODO : 5 bytes + 3 bytes, where each of six nibbles represents size (in words) of successive children?? (16 words max each)
      let !histSiblingOffs' = case toPtrs of
              [] -> histSiblingOffs
              (toPtr0:toPtrsN) -> foldl' (flip go) histSiblingOffs toPtrsN where
                 go toPtr = Map.insertWith (+) bucket 1 where
                   bucket = (offsetFromBucket toPtr0 toPtr, numFieldsBucket)

      -- histogram of heap residency, by closure size (divide to get counts):
      let !histClosureSizes' = Map.insertWith (+) (min size (16*8)) size histClosureSizes
      
      -- ...whereas if all child pointers of a closure had to be equal sized
      -- and signed, what size would we need for all the pointers in this
      -- closure? (these will all be positive bit width buckets):
      let !histMaxOffs' = insrt $ map offsetFromPtrBucket toPtrs
            where insrt [] = histMaxOffs
                  insrt offs
                    -- ...turns out not:
                    -- | any (<=0) offs = error "I really don't think we expect non-positive offsets here!"
                    | otherwise = Map.insertWith (+) (maximum $ map abs offs, numFieldsBucket) 1 histMaxOffs

      -- how many pointers are there that are: 1) last, and 2) point to the
      -- immediately adjacent heap object?:
      -- NOTE: first is about the same, but actually has a smaller count here...
      --       I'm not sure why that should be... I guess if scav/evac is a
      --       breadth-first traversal then we only get a tail that is compact
      --       (except for singe-pointer closures)?
      let !lastPointingNext' = lastPointingNext + case reverse toPtrs of
            (toPtr:_) | toPtr - ptr == fromIntegral size -> 1
            _                                            -> 0

      let !blockGraph' = foldl' (flip $ IM.insertWith ins ourBlock) blockGraph $ map toSingletonMap toPtrs
            where (ourBlock, _) = getKeyPair cp
                  ins newSingleMap existingMap
                    | Map.size existingMap >= maxBlockGraphEdgesToRecord = existingMap
                    | otherwise = Map.unionWith (+) newSingleMap existingMap
                  toSingletonMap toPtr = Map.fromList [(fst $ getKeyPair $ UntaggedClosurePtr toPtr, 1)]

      put AnalyzePointerCompressionStats {
            infoTableMin = infoTableMin', 
            infoTableMax = infoTableMax', 
            infoPointers = infoPointers', 
            lastPointingNext = lastPointingNext', 
            histFirst = histFirst', 
            histLast = histLast', 
            histOffs = histOffs', 
            histSiblingOffs = histSiblingOffs', 
            histMaxOffs = histMaxOffs',
            blockGraph = blockGraph',
            histClosureSizes = histClosureSizes'
            }

      continue
      where
        -- We'll use buckets for 1-, 2-, 4-, and 8-byte range (positive and
        -- negative). We'll leave two extra bits for tags: one for what we'd
        -- lose if heap objects became 4-byte-aligned, and one for a
        -- possibly-required sign bit or another tag.
        bitBuckets = [6, 14, 30]
        offsetFromPtrBucket :: Word64 -> Int
        offsetFromPtrBucket = offsetFromBucket ptr

        offsetFromBucket refPtr toPtr = signum offs * goBucket (abs offs) bitBuckets where
            goBucket _ []       = 64
            goBucket offsPos (l:ls)
              | offsPos <= 2^l  = l
              | otherwise       = goBucket offsPos ls

            -- distance (possibly negative) from `refPtr` to `toPtr`
            offs :: Int
            offs = fromIntegral toPtr - fromIntegral refPtr

-- copied from GHC.Debug.Trace:
getKeyPair :: ClosurePtr -> (Int, Word16)
getKeyPair cp =
  let BlockPtr raw_bk = applyBlockMask cp
      bk = fromIntegral raw_bk `div` 8
      offset = getBlockOffset cp `div` 8
  in (bk, fromIntegral offset)


-- ================================================================================
-- https://gitlab.haskell.org/ghc/ghc/-/issues/14461 
-- https://gitlab.haskell.org/ghc/ghc/-/wikis/nested-closures 
-- https://gitlab.haskell.org/ghc/ghc/-/wikis/Sharing-Closure-Environments-in-STG 

-- For:         (!visited, !pointersTotal, !identicalPtrs):
-- (50774469, _       , 11396500) = for all closure types, before Rules shrunk
--
-- (31967878, 88165269, 33285652)   ...and after
-- (15467397, 51118660, 31381916) = for just parents that isFunLike
-- (15467397, 51118660, 31367929) = for parent and child that isFunLike
pAnalyzeNestedClosureFreeVars :: Debuggee -> IO ()
pAnalyzeNestedClosureFreeVars e = do
  pause e
  runTrace e $ do
    _bs <- precacheBlocks
    liftIO $ hPutStrLn stderr "!!!!! Done precacheBlocks !!!!!"
    roots <- gcRoots
    liftIO $ hPutStrLn stderr "!!!!! Done gcRoots !!!!!"

    -- since I got tired of threading state below...
    mutState <- liftIO $ newMVar (mempty :: Map.Map InfoTablePtr Int)

    out@(_closuresVisited, _pointersTotal, _childPointersInParent, _hist)
       <- flip execStateT (0::Int,0::Int,0::Int, mempty::Map.Map (Int,Int) Int) $
            traceFromM emptyTraceFunctions{closTrace = closTraceFunc mutState} roots

    liftIO $ print out
    liftIO $ putStrLn "==========================="
    mp <- liftIO $ takeMVar mutState
    forM_ (sort $ map swap $ Map.toList mp) $ \(cnt, tid) -> do
        liftIO $ print ("COUNT", cnt)
        getSourceInfo tid >>= mapM_ (liftIO . print)
    liftIO $ putStrLn "==========================="
    byLoc <- forM (Map.toList mp) $ \(tid, cnt) -> do
        getSourceInfo tid >>= \case
          Nothing -> return Nothing
          Just si -> return $ Just (infoPosition si, cnt)
    forM_ (reverse $ sort $ map swap $ Map.toList $ Map.fromListWith (+) $ catMaybes byLoc) $ \(cnt, pos) -> do
        liftIO $ putStrLn pos
        liftIO $ print ("COUNT", cnt)


  where
    closTraceFunc mutState _parentPtr (DCS _ parentClos) continue = do

      when (isFunLike parentClos || analyzeAllClosureTypes) $ do
          parentClosPtrs <- getAllPtrs parentClos

          -- childFieldsHist: (count_fields_in_closure, count_fields_in_closure in parent) -> count_of_closures_like_this
          (!visited, !pointersTotal, !identicalPtrs, !childFieldsHist) <- get

          (childPointersInParent, childFieldsHist_toAdd) <- lift $ flip execStateT (0, mempty) $
              -- for each of our pointers...
              void $ flip (quintraverse pure pure pure pure) parentClos $ \ toPtr-> do
                (!childPointersInParent, !childFieldsHist_toAdd) <- get
                -- ...follow and collect child's pointers
                (DCS _ childClos) <- lift $ dereferenceClosure toPtr
                when (isFunLike childClos || analyzeAllClosureTypes) $ do
                    childClosPtrs <- getAllPtrs childClos
                    let !ourPointersInParent = Set.size (childClosPtrs `Set.intersection` parentClosPtrs)
                        !childPointers = Set.size childClosPtrs
                    put $! (childPointersInParent+ourPointersInParent, 
                            (childPointers, ourPointersInParent) : childFieldsHist_toAdd
                           )
                    when (childPointers == 1 && ourPointersInParent == 1) $ do
                        let tid = tableId $ info childClos
                        liftIO $ modifyMVar_ mutState $
                            return . Map.insertWith (+) tid 1

          put (visited+1, 
               pointersTotal+Set.size parentClosPtrs , 
               identicalPtrs+childPointersInParent,
               foldl' (\mp k-> Map.insertWith (+) k 1 mp) childFieldsHist childFieldsHist_toAdd
              )
      continue

    -- Do we want to analyze all closure types, regardless of whether they are function-like?
    analyzeAllClosureTypes = False
    
    isFunLike = \case
      FunClosure{} -> True
      ThunkClosure{} -> True
      _ -> False

    getAllPtrs clos = lift $ flip execStateT mempty $
          void $ flip (quintraverse pure pure pure pure) clos $ \ ptr-> do
              ptrs <- get
              put $! Set.insert ptr ptrs

----------------------------------------------------------

-- Most of the time does the parent info pointer uniquely determine the info pointer of child?
pInfoTableTree :: Debuggee -> IO ()
pInfoTableTree e = do
  pause e
  runTrace e $ do
    _bs <- precacheBlocks
    liftIO $ hPutStrLn stderr "!!!!! Done precacheBlocks !!!!!"
    roots <- gcRoots
    liftIO $ hPutStrLn stderr "!!!!! Done gcRoots !!!!!"

    -- for each info pointer, store the first set of info-pointers for child objects seen
    -- for subesquent objects, increment either the MATCH or NO_MATCH counters
    mp <- flip execStateT mempty $ 
       traceFromM emptyTraceFunctions{closTrace = closTraceFunc} roots
    F.for_ (Map.elems mp) $ \(_, matchedCount, noMatchCount) -> do
        liftIO $ print (matchedCount, noMatchCount)

  where
    closTraceFunc _ (DCS _ clos) continue = do
      mp <- get
      let (InfoTablePtr iptr) = tableId $ info clos

      -- info pointers of each dereferenced child pointer
      toIptrs <- fmap reverse $ lift $ flip execStateT [] $
          void $ flip (quintraverse pure pure pure pure) clos $ \toPtr-> do
              stack <- get
              (DCS _ childClos) <- lift $ dereferenceClosure toPtr
              let (InfoTablePtr childIptr) = tableId $ info childClos
              put (childIptr:stack)
      -- Don't bother if there are no pointers
      unless (null toIptrs) $ do
          let mp' = Map.insertWith merge iptr (toIptrs, 0::Int, 0::Int) mp
              merge _ (toIptrs_already, !matchedCount, !noMatchCount)
                | toIptrs_already == toIptrs = (toIptrs, matchedCount+1, noMatchCount)
                | otherwise                  = (toIptrs, matchedCount, noMatchCount+1)
          put $! mp'
      continue

----------------------------------------------------------

-- some stuff about info tables:
--   - how many are for static closures, vs dynamic?
pDistinctInfoTableAnalysis :: Debuggee -> IO ()
pDistinctInfoTableAnalysis e = do
  pause e
  runTrace e $ do
    _bs <- precacheBlocks
    liftIO $ hPutStrLn stderr "!!!!! Done precacheBlocks !!!!!"
    roots <- gcRoots
    liftIO $ hPutStrLn stderr "!!!!! Done gcRoots !!!!!"

    (static, dynamic) <- flip execStateT (mempty, mempty) $ 
       traceFromM emptyTraceFunctions{closTrace = closTraceFunc} roots
    liftIO $ do
        putStrLn "(static_count, dynamic_count):"
        print (Set.size static, Set.size dynamic)

  where
    closTraceFunc _ (DCS (Size size) clos) continue = do
      (!static, !dynamic) <- get
      let (InfoTablePtr iptr) = tableId $ info clos

      -- assume if closure is word-size it must be STATIC
      if size == 8
         then put (Set.insert iptr static, dynamic)
         else put (static, Set.insert iptr dynamic)
      continue

----------------------------------------------------------

-- “A simple algorithm for finding frequent elements in streams and bags”
-- https://www.cs.umd.edu/class/spring2018/cmsc644/karp.pdf
--
-- We expect this to return all elements each composing greater than
-- `1/(stateSize+1)` of the input, should any exist. e.g. when stateSize = 2
-- and we have 99 elements, this will return any occurring more than 33 times.
-- A second pass is required to get the actual counts for the candidates
-- identified, if required.
--
-- (I try to match the pseudocode here, though it’s not terribly efficient)
data FrequentElems a = FrequentElems
    { excessCounts :: (Map.Map a Int)
    -- ^ invariant: Map.size excessCounts <= stateSize
    , stateSize :: Int
    -- ^ static
    } deriving (Show)

emptyFrequentElems :: (Ord a)=> Int -> FrequentElems a
emptyFrequentElems = FrequentElems mempty

insertFrequentElems :: (Ord a)=> FrequentElems a -> a -> FrequentElems a
insertFrequentElems FrequentElems{..} a =
    let excessCounts' = Map.insertWith (+) a 1 excessCounts --now possibly over capacity
     in if Map.size excessCounts' > stateSize
           -- (implies we inserted a new value above)
           then let excessCounts'' = Map.filter (> 0) $ 
                      fmap (subtract 1) $ excessCounts'
                 in FrequentElems excessCounts'' stateSize
           else FrequentElems excessCounts' stateSize

-- For each closure type (i.e. grouping by info pointer), How many of these
-- exist with the same pointer arguments?
pCommonPtrArgs :: Debuggee -> IO ()
pCommonPtrArgs e = do
  pause e
  runTrace e $ do
    _bs <- precacheBlocks
    liftIO $ hPutStrLn stderr "!!!!! Done precacheBlocks !!!!!"
    roots <- gcRoots
    liftIO $ hPutStrLn stderr "!!!!! Done gcRoots !!!!!"

    -- for each info pointer, select the candidates for most frequent pointer
    -- argument occurrences
    liftIO $ hPutStrLn stderr "Tracing to collect frequent elems candidates..."
    candidatesByInfo <- flip execStateT (mempty :: Map.Map Word64 (FrequentElems [ClosurePtr])) $
       traceFromM emptyTraceFunctions{closTrace = traceFreqCandidates} roots
    -- For each of the candidates identified above, count the actual
    -- occurrences of the potentially frequently-occurring closures,
    -- incrementing either the MATCH or NO_MATCH counters
    let candidatesKeys = fmap (Map.keys . excessCounts) candidatesByInfo
    liftIO $ hPutStrLn stderr "Tracing again to count frequencies..."
    mp <- flip execStateT mempty $ 
       traceFromM emptyTraceFunctions{closTrace = traceCountFreq candidatesKeys} roots

    -- filter out where just a single occurrences of that closure type, to reduce noise
    let nonSingletons = Map.filter (\(x,y) -> x + y /= 0) mp
        (matchesL, unmatchesL) = unzip $ Map.elems nonSingletons
    liftIO $ do
        print ("non-singleton info entries", length nonSingletons)
        print ("matches total", sum matchesL)
        print ("nonmatches total", sum unmatchesL)

    let bigMatches = sort $ map (\(iptr,(matches,_)) -> (matches,iptr)) $ Map.toList $ Map.filter ((>10000) . fst) nonSingletons
    F.for_ bigMatches $ \(matches, iptr) -> do
      mbSourceInfo <- getSourceInfo $ InfoTablePtr iptr
      liftIO $ print (matches, mbSourceInfo)
    -- TODO
    --   - for candidates:
    --       excess counts + matched % + total count
    --   - matches / non-matches totals

  where
    -- If we imagine the RTS can do some caching / hash consing,  how many
    -- distinct closure configurations should we cache per-infotable entry?
    -- This also corresponds with the guarantees outlined above wrt frequent
    -- elements, e.g. 2 here means if there exists to elements did you compose
    -- more than 33% of the total closures, both are guaranteed to be in the
    -- cache  after we iterate over the heap.
    cacheSize = 4
    frequencySingleton = insertFrequentElems (emptyFrequentElems cacheSize)

    -- get the potentially-frequent pointer arguments, by info table entry
    traceFreqCandidates _ (DCS _ clos) continue = do
      freqElemsMap <- get
      let (InfoTablePtr iptr) = tableId $ info clos
      -- child pointers of closure
      toPtrs <- fmap reverse $ lift $ flip execStateT [] $
          void $ flip (quintraverse pure pure pure pure) clos $ \toPtr-> do
              stack <- get
              put (toPtr:stack)

      -- Don't bother if there are no pointers
      unless (null toPtrs) $ do
          let freqElemsMap' = Map.insertWith merge iptr (frequencySingleton toPtrs) freqElemsMap
              merge _ freq = insertFrequentElems freq toPtrs
          put $! freqElemsMap'
      continue

    -- actually count occurrence frequency of those candidates, on a second pass:
    traceCountFreq candidatesKeys _ (DCS _ clos) continue = do
      mp <- get
      let (InfoTablePtr iptr) = tableId $ info clos
      -- child pointers of closure
      toPtrs <- fmap reverse $ lift $ flip execStateT [] $
          void $ flip (quintraverse pure pure pure pure) clos $ \toPtr-> do
              stack <- get
              put (toPtr:stack)

      case Map.lookup iptr candidatesKeys of
        Just candidates -> do
          let mp' = Map.insertWith merge iptr (0::Int, 0::Int) mp
              -- mark whether this set of child pointers would have been cached
              -- by any of the candidates:
              merge _ (!matchedCount, !noMatchCount)
                -- ...record pointer count...
                | toPtrs `elem` candidates = (matchedCount+length toPtrs, noMatchCount)
                | otherwise                = (matchedCount, noMatchCount+length toPtrs)
                -- ...vs just closure count:
                -- | toPtrs `elem` candidates = (matchedCount+1, noMatchCount)
                -- | otherwise                = (matchedCount, noMatchCount+1)
          put $! mp'
        Nothing -> pure ()
      continue


----------------------------------------------------------

-- 
pPointersToPointers :: Debuggee -> IO ()
pPointersToPointers e = do
  pause e
  runTrace e $ do
    _bs <- precacheBlocks
    liftIO $ hPutStrLn stderr "!!!!! Done precacheBlocks !!!!!"
    roots <- gcRoots
    liftIO $ hPutStrLn stderr "!!!!! Done gcRoots !!!!!"

    (pointersToPointersCount, pointersToDoubleWordCount) <- flip execStateT (0::Int, 0::Int) $
       traceFromM emptyTraceFunctions{closTrace} roots
    liftIO $ print ("pointersToPointersCount", pointersToPointersCount)
    liftIO $ print ("pointersToDoubleWordCount", pointersToDoubleWordCount)
  where
    closTrace _ (DCS _ clos) continue = do
      -- how many child pointers are just dereference to pointers themselves?
      void $ flip (quintraverse pure pure pure pure) clos $ \toPtr-> do
        (pointersToPointersCount, pointersToDoubleWordCount) <- get
        (DCS (Size childSize) _) <- lift $ dereferenceClosure toPtr
        -- size should include info pointer, so this should work:
        when (childSize == 8) $
          -- I think true means this is a static object
          put $! (pointersToPointersCount + 1, pointersToDoubleWordCount)
        when (childSize == 16) $
          put $! (pointersToPointersCount, pointersToDoubleWordCount+1)
      continue
