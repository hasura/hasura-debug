{-# OPTIONS_GHC -fno-warn-orphans -Wno-unused-imports#-}
{-# LANGUAGE LambdaCase, RecordWildCards #-}
{-# LANGUAGE RecordPuns #-}
module FreeVarAnalysis where

import GHC.Debug.Client hiding (DebugM)
import GHC.Debug.Client.Monad hiding (DebugM)
import GHC.Debug.Client.Monad.Simple (DebugM(..))
import GHC.Debug.Count (parCount)


-- import GHC.Debug.Profile
import GHC.Debug.Dominators (retainerSize)
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

newtype SharingInfoResult = SharingInfoResult { unSharingInfoResult :: LazyMap.Map SharedClosureInfo Int }

instance Semigroup SharingInfoResult where
  (<>) :: SharingInfoResult -> SharingInfoResult -> SharingInfoResult
  l <> r = SharingInfoResult $ Map.unionWith (+) (unSharingInfoResult l) (unSharingInfoResult r)

instance Monoid SharingInfoResult where
  mempty = SharingInfoResult mempty

addSharingResult :: SharingInfoResult -> SharedClosureInfo -> SharingInfoResult
addSharingResult (SharingInfoResult result_count) cl_info = SharingInfoResult $ Map.insertWith (+) cl_info 1 result_count

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

    census <- parCount roots
    liftIO $ print census

    -- since I got tired of threading state below...
    mutState <- liftIO $ newMVar (mempty :: Map.Map InfoTablePtr Int)

    hist
       <- flip execStateT (mempty::SharingInfoResult) $
            traceFromM emptyTraceFunctions{closTrace = closTraceFunc mutState} roots

    -- liftIO $ print out
    -- liftIO $ putStrLn "==========================="
    -- liftIO $ putStrLn "== One pointer that is also in parent"
    -- mp <- liftIO $ takeMVar mutState
    -- forM_ (sort $ map swap $ Map.toList mp) $ \(cnt, tid) -> do
    --     liftIO $ print ("COUNT", cnt)
    --     getSourceInfo tid >>= mapM_ (liftIO . print)

    -- liftIO $ putStrLn "==========================="
    -- byLoc <- forM (Map.toList mp) $ \(tid, cnt) -> do
    --     getSourceInfo tid >>= \case
    --       Nothing -> return Nothing
    --       Just si -> return $ Just (infoPosition si, cnt)
    -- forM_ (reverse $ sort $ map swap $ Map.toList $ Map.fromListWith (+) $ catMaybes byLoc) $ \(cnt, pos) -> do
    --     liftIO $ putStrLn pos
    --     liftIO $ print ("COUNT", cnt)

    -- Interesting data from the histogram
    let intestingHistData = Map.filterWithKey
                              (\(SharedClosureInfo our_ptrs in_parent _is_thunk _par_tbl _itbls _fvs) count ->
                                  -- Ignore results that only occur once
                                  count > 1 &&
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
      let sorted_data = reverse $ sortOn (\(SharedClosureInfo{ shared_with_parent = shared},count)-> shared * count ) $ Map.toList intestingHistData
      let analyze_one ptr_sum ((SharedClosureInfo
              { ptrs = our_ptrs
              , shared_with_parent = in_parent
              -- , is_thunk
              , par_itbl
              , child_itbl
              , fv_info}),count) = do
            -- We need one ptr to point at the parent so at best we can save count * (in_parent-1)
            let max_ptrs_saved = (count * (in_parent-1))
            let get_loc itbl = getSourceInfo $ tableId itbl
            prnt_loc <- get_loc par_itbl
            chld_loc <- get_loc child_itbl
            liftIO $ putStrLn $ "ptrs:" <> show our_ptrs <> " shared_ptrs:" <> show in_parent <> " ptrs saved potential:" <> show max_ptrs_saved <> "(wds)" <>
                                " fv_infos:" <> show fv_info <>
                                " "<> maybe "" show prnt_loc <>
                                " "<> maybe "" show chld_loc
            return $ ptr_sum + max_ptrs_saved
      max_saved <- foldM analyze_one 0 sorted_data
      liftIO $ putStrLn $ "Max wds saved: " <> show max_saved <> show " (" <> show (div max_saved (1024^(2::Int))) <> "MB)"



      -- flip mapM_ (sorted_data) $ \(hist@(SharedClosureInfo _our_ptrs in_parent _is_thunk),count) -> do



  where
    closTraceFunc :: a
                  -> ClosurePtr
                  -> SizedClosure
                  -> StateT SharingInfoResult DebugM b1
                  -> StateT SharingInfoResult DebugM b1
    closTraceFunc _mutState parentPtr (DCS _ parentClos) continue = do

      when (isFunLike parentClos || analyzeAllClosureTypes) $ do
          parentClosPtrs <- getAllPtrs parentClos
          let parent_itbl = info parentClos

          (!childFieldsHist) <- get

          (childFieldsHist_toAdd) <- lift $ flip execStateT (mempty) $
              -- for each of our pointers...
              void $ traverseSubClosures parentClos $ \ toPtr-> do
                (!childFieldsHist_toAdd) <- get

                -- ...follow and collect child's pointers
                (DCS _ childClos) <- lift $ dereferenceClosure toPtr
                let child_itbl = info childClos
                -- If we have a closure containing a reference the "child" will look like it
                -- shares all fvs with the parent but there is nothing we can do about it.
                when (toPtr /= parentPtr &&
                      (isFunLike childClos || analyzeAllClosureTypes))
                      $ do
                    childClosPtrs <- getAllPtrs childClos
                    let !ourPointersInParent = (childClosPtrs `Set.intersection` parentClosPtrs)
                        !outPointersInParentCnt = Set.size ourPointersInParent
                        !childPointers = Set.size childClosPtrs
                        !chld_is_thunk = isThunk childClos

                    when (outPointersInParentCnt > 0) $ do
                      fv_infos <- forM (Set.elems ourPointersInParent) $ \shared_cls -> do
                        (DCS _ shared_cls) <- lift $ dereferenceClosure shared_cls
                        -- let itbl = info shared_cls
                        src_loc <- lift $ getSourceInfo $ tableId $ info shared_cls
                        -- liftIO $ putStrLn $ show (infoType <$> src_loc)
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
                      let !histData = this_data : childFieldsHist_toAdd
                      put $! histData

          put $
            foldl' addSharingResult childFieldsHist childFieldsHist_toAdd

      continue

    -- Do we want to analyze all closure types, regardless of whether they are function-like?
    analyzeAllClosureTypes = False

    isThunk = \case
      ThunkClosure{} -> True
      _ -> False

    isFunLike = \case
      FunClosure{} -> True
      ThunkClosure{} -> True -- Thunks might not evaluate to functions but they might.
                             -- So including them seems reasonable.
      _ -> False

    -- getAllPtrs :: DebugClosure b d g i ClosurePtr
    --               -> StateT
    --                    (Int, Int, Int, LazyMap.Map SharedClosureInfo Int) DebugM (Set.Set ClosurePtr)
    getAllPtrs clos = lift $ flip execStateT mempty $
          void $ traverseSubClosures clos $ \ ptr-> do
              ptrs <- get
              put $! Set.insert ptr ptrs

----------------------------------------------------------
