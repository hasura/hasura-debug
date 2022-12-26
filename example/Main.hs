{-# LANGUAGE BangPatterns #-}
module Main where

import Control.Concurrent
import GHC.Debug.Stub

main :: IO ()
main = withGhcDebug $ do
    let size = 2^(6::Int) :: Int -- power of two assumed below
        leafVals = [1..size]

    let !tree = balancedTree size leafVals

    putStrLn "Pausing for a long time so you can take a snapshot. CTRL-C from here to exit"
    threadDelay $ 1000*1000*1000
    -- Just make sure stuff is retained in memory :
    print tree
    where
        balancedTree 1 [n]
          | even n = Leaf $ smallLeaf n
          | otherwise = Leaf $ largeLeaf n
        balancedTree len ns =
            let len' = len `div` 2
                (nsL, nsR) = splitAt len' ns
             in Branch (balancedTree len' nsL) (balancedTree len' nsR)



-- A simple strict tree structure, that we should be able to understand by looking at a graph
data Tree = Branch !Tree !Tree
          | Leaf !LeafNode
          deriving Show

data LeafNode = SmallLeaf !Int
              | LargeLeaf !Int !Int !Int !Int !Int !Int !Int !Int -- 64bytes
              deriving Show

-- We'll generate leaves from two different source code locations, and we
-- expect some of the leaves to be much larger than others ( due to the
-- unpacked Ints)

smallLeaf :: Int -> LeafNode
smallLeaf n = SmallLeaf n

largeLeaf :: Int -> LeafNode
largeLeaf n = LargeLeaf n n n n n n n n
