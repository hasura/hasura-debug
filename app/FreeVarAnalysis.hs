{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE LambdaCase, RecordWildCards #-}
module FreeVarAnalysis where

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

import Util

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

data IPair =
    IPair { ip1 :: !Int, ip2 :: !Int }
    deriving (Eq,Ord,Show)

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
       <- flip execStateT (0::Int,0::Int,0::Int, mempty::Map.Map IPair Int) $
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
    closTraceFunc :: MVar (LazyMap.Map InfoTablePtr Int)
                  -> p
                  -> DebugClosureWithExtra x b d g i ClosurePtr
                  -> StateT (Int, Int, Int, LazyMap.Map IPair Int) DebugM b1
                  -> StateT (Int, Int, Int, LazyMap.Map IPair Int) DebugM b1
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
                            (IPair childPointers ourPointersInParent) : childFieldsHist_toAdd
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
