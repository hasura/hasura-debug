{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE LambdaCase, RecordWildCards #-}
module Main where

import GHC.Debug.Client hiding (DebugM)
import GHC.Debug.Client.Monad hiding (DebugM)
import GHC.Debug.Snapshot


-- import Control.Monad
-- import Debug.Trace
import Control.Exception
import Control.Concurrent

-- import System.Process
import System.Environment
import System.IO

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
       let limI = read limDirty :: Int
           _lim | limI == 0 = Nothing
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
