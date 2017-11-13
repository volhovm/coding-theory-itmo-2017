-- | asoenuh

module Main where

import           Universum

import           Part2     (task21)

main :: IO ()
main = do
    putText "starting"
    print $ task21 6 4
    putText "done"
