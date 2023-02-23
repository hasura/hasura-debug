{-# OPTIONS_GHC -fno-warn-orphans -Wno-unused-imports#-}
{-# LANGUAGE LambdaCase, RecordWildCards #-}
{-# LANGUAGE NamedFieldPuns #-}
module FreeVarAnalysis where

import GHC.Debug.Client hiding (DebugM)
import GHC.Debug.Client.Monad hiding (DebugM)
import GHC.Debug.Client.Monad.Simple (DebugM(..))
import GHC.Debug.Count (parCount)


-- import GHC.Debug.Profile
import GHC.Debug.Dominators (retainerSize)
-- import GHC.Debug.Trace
import GHC.Debug.ParTrace
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

import Util
import Data.Foldable (Foldable(foldMap'))
import GHC.Debug.Retainers (findRetainers)

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

-- | Information about a kind of closure who might benefit from sharing FVs.
data SharedClosureInfo =
    SharedClosureInfo
          { ptrs :: !Int
          , shared_with_parent :: !Int
          , is_thunk :: !Bool
          , par_itbl :: !StgInfoTableWithPtr
          , child_itbl :: !StgInfoTableWithPtr
          , fv_info :: !(Set.Set (String))  }
    deriving (Show)

instance Eq SharedClosureInfo where
  x == y = par_itbl x == par_itbl y && child_itbl x == child_itbl y

instance Ord SharedClosureInfo where
  compare x y = compare (par_itbl x, child_itbl x) (par_itbl y, child_itbl y)

-- | Aggreate data about closures
newtype SharingInfoResult = SharingInfoResult { unSharingInfoResult :: LazyMap.Map SharedClosureInfo SharingSample }

instance Semigroup SharingInfoResult where
  (<>) :: SharingInfoResult -> SharingInfoResult -> SharingInfoResult
  l <> r = SharingInfoResult $ Map.unionWith (<>) (unSharingInfoResult l) (unSharingInfoResult r)

instance Monoid SharingInfoResult where
  mempty = SharingInfoResult mempty

data SharingSample = SharingSample
  { sample_samples :: (Set.Set ClosurePtr)
  , sample_count :: !Int
  } deriving (Show)

sampleLimit :: Int
sampleLimit = 5

instance Semigroup SharingSample where
  (SharingSample samples_x count_x) <> (SharingSample samples_y count_y)
    = SharingSample samples (count_x + count_y)
    where
      samples
        | Set.size samples_x >= sampleLimit = samples_x
        | Set.size samples_y >= sampleLimit = samples_y
        | otherwise = Set.fromList $ take sampleLimit (Set.toList samples_x <> Set.toList samples_y)

instance Monoid SharingSample where
  mempty = SharingSample mempty 0

addSharingResult :: SharingInfoResult -> (SharedClosureInfo,ClosurePtr) -> SharingInfoResult
addSharingResult (SharingInfoResult result_count) (cl_info,ptr) = SharingInfoResult $ Map.insertWith (<>) cl_info (SharingSample (Set.singleton ptr) 1) result_count

-- traverseSubClosures
traverseSubClosures :: (Quintraversable m, Applicative f)
                    => m b d g i ClosurePtr -> (ClosurePtr -> f k) -> f (m b d g i k)
traverseSubClosures f = flip (quintraverse pure pure pure pure) f

pAnalyzeNestedClosureFreeVars :: Debuggee -> IO ()
pAnalyzeNestedClosureFreeVars e = do
  pause e
  runTrace e $ do
    _bs <- precacheBlocks
    liftIO $ hPutStrLn stderr "!!!!! Done precacheBlocks !!!!!"
    roots <- gcRoots
    liftIO $ hPutStrLn stderr "!!!!! Done gcRoots !!!!!"

    -- If we want to know the size of the heap uncomment the two statements below.
    -- census <- parCount roots
    -- liftIO $ print census

    -- since I got tired of threading state below...
    mutState <- liftIO $ newMVar (mempty :: Map.Map InfoTablePtr Int)

    let info_roots = map (ClosurePtrWithInfo ()) roots
    let traceFunctions :: TraceFunctionsIO () (SharingInfoResult)
        traceFunctions = (emptyTraceFunctionsIO (const mempty)) {closTrace = parClosTraceFunc mutState}
    hist
      --  <- traceParFromM emptyTraceFunctions{closTrace = parClosTraceFunc mutState} roots
       <- traceParFromM traceFunctions info_roots

    -- Interesting data from the histogram
    let intestingHistData = Map.filterWithKey
                              (\(SharedClosureInfo our_ptrs in_parent _is_thunk _par_tbl _itbls _fvs) count ->
                                  -- Ignore results that only occur once
                                  (sample_count count) > 1 &&
                                  -- Ignore results that don't allow sharing
                                  in_parent > 0 &&
                                  -- There is no point in sharing a single pointer
                                  -- we would just replace a pointer to the payload
                                  -- with a pointer to the parent
                                  our_ptrs > 1)
                              $ unSharingInfoResult hist
    do
      liftIO $ putStrLn "==========================="
      liftIO $ putStrLn "== Sharing histogram"
      let sorted_data = reverse $ sortOn (\(SharedClosureInfo{ shared_with_parent = shared},sample_data)-> shared * (sample_count sample_data) ) $ Map.toList intestingHistData
      let reportOne ptr_sum ((SharedClosureInfo
              { ptrs = our_ptrs
              , shared_with_parent = in_parent
              -- , is_thunk
              , par_itbl
              , child_itbl
              , fv_info = _}),sample_data) = do
            -- We need one ptr to point at the parent so at best we can save count * (in_parent-1)
            let max_ptrs_saved = ((sample_count sample_data) * (in_parent-1))
            let get_loc itbl = getSourceInfo $ tableId itbl
            prnt_loc <- get_loc par_itbl
            chld_loc <- get_loc child_itbl
                            -- Basic info
            liftIO $ putStrLn $
                "parent:"<> maybe "" show prnt_loc <>
                "\n\tchild:"<> maybe "" show chld_loc <>
                "\n\tsamples:"<> show sample_data <>
                -- Info about free variables
                -- "\n\tfv_infos:" <> show fv_info <>
                "\n\tptrs:" <> show our_ptrs <> " shared_ptrs:" <> show in_parent <> " ptrs saved potential:" <> show max_ptrs_saved <> "(wds)"
            -- analyzePathsTo roots (head $ (Set.elems $ sample_samples sample_data) )
            return $ ptr_sum + max_ptrs_saved
      max_saved <- foldM reportOne 0 sorted_data
      liftIO $ putStrLn $ "Max wds saved: " <> show max_saved <> show " (" <> show (div (max_saved*8) (1024^(2::Int))) <> "MB)"

  where
    parClosTraceFunc :: mut_state_
                  -> ClosurePtr
                  -> (DebugClosureWithExtra x b d g i ClosurePtr)
                  -> ()
                  -> DebugM ((),SharingInfoResult, DebugM () -> DebugM ())
    parClosTraceFunc _mutState parentPtr (DCS _ parentClos) _partial_result = do
        child_infos <-
                if (isFunLike parentClos || analyzeAllClosureTypes)
                    then analyzeOneClosure parentPtr parentClos
                    else pure []

        let sharing_info = foldl' addSharingResult (mempty) child_infos

        return ((), sharing_info, id)

-- Do we want to analyze all closure types, regardless of whether they are function-like?
analyzeAllClosureTypes :: Bool
analyzeAllClosureTypes = False

isThunk :: DebugClosure srt pap string s b -> Bool
isThunk = \case
  ThunkClosure{} -> True
  _ -> False

isFunLike :: DebugClosure srt pap string s b -> Bool
isFunLike = \case
  FunClosure{} -> True
  ThunkClosure{} -> True -- Thunks might not evaluate to functions but they might.
                          -- So including them seems reasonable.
  _ -> False

-- getAllPtrs :: DebugClosure b d g i ClosurePtr
--               -> StateT
--                    (Int, Int, Int, LazyMap.Map SharedClosureInfo Int) DebugM (Set.Set ClosurePtr)
getAllPtrs :: (Quintraversable m1, Monad m2) => m1 b d g i ClosurePtr -> m2 (Set.Set ClosurePtr)
getAllPtrs clos = flip execStateT mempty $
      void $ traverseSubClosures clos $ \ ptr-> do
          ptrs <- get
          put $! Set.insert ptr ptrs

-- This is hugely expensive. Use with care.
analyzePathsTo :: [ClosurePtr] -> ClosurePtr -> DebugM ()
analyzePathsTo roots ptr = do
  paths <- findRetainers (Just 2) roots (\p _ -> return (p == ptr))
  liftIO $ putStrLn $ ("Found paths to " <> show ptr <> "\n")
  forM_ paths $ \path -> do
    liftIO $ putStrLn "Path: "
    forM_ path $ \node -> do
        clos <- dereferenceClosure node
        loc <- getSourceLoc clos
        liftIO $ putStr $ "\n\t-> " <> (case infoPosition <$> loc of
            Just loc_str -> loc_str
            Nothing -> show (clos,loc))

analyzeOneClosure :: p -> DebugClosure b d g i ClosurePtr -> DebugM [(SharedClosureInfo,ClosurePtr)]
analyzeOneClosure _parentPtr parentClos = do
    let parent_itbl = info parentClos

    flip execStateT (mempty) $ do
        parentClosPtrs <- getAllPtrs parentClos

        -- for each of our pointers...
        void $ traverseSubClosures parentClos $ \ toPtr-> do
            (!childFieldsHist_toAdd) <- get

            -- ...follow and collect child's pointers
            (DCS _ childClos) <- lift $ dereferenceClosure toPtr
            let child_itbl = info childClos
            when ((isFunLike childClos || analyzeAllClosureTypes)) $ do
                childClosPtrs <- getAllPtrs childClos
                let !ourPointersInParent = (childClosPtrs `Set.intersection` parentClosPtrs)
                    !outPointersInParentCnt = Set.size ourPointersInParent
                    !childPointers = Set.size childClosPtrs
                    !chld_is_thunk = isThunk childClos

                when (outPointersInParentCnt > 0) $ do
                    fv_infos <- forM (Set.elems ourPointersInParent) $ \shared_cls_ptr -> do
                        (DCS _ shared_cls) <- lift $ dereferenceClosure shared_cls_ptr
                        src_loc <- lift $ getSourceInfo $ tableId $ info shared_cls
                        return (infoType <$> src_loc)
                    let fv_info_set = Set.fromList $ catMaybes fv_infos
                    let this_data = SharedClosureInfo {
                        ptrs = childPointers,
                        shared_with_parent = outPointersInParentCnt,
                        is_thunk = chld_is_thunk,
                        par_itbl= parent_itbl,
                        child_itbl = child_itbl,
                        fv_info = fv_info_set
                        }
                    let !histData = (this_data,toPtr) : childFieldsHist_toAdd
                    put $! histData
----------------------------------------------------------
