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

import Util
import FreeVarAnalysis

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
        --  pAnalyzePointerCompression
         pAnalyzeNestedClosureFreeVars
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
