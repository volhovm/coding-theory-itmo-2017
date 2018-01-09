-- | asoenuh

module Main where

import           Universum

import           Control.Concurrent.Async
import           Data.List
import           Lib

main :: IO ()
main = do
    task42 500000
