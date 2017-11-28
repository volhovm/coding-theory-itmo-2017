-- | asoenuh

module Main where

import Universum

import Part2

main :: IO ()
main = do
    let n = 18
    let k = 3
    print $ findDRange n k
    let h = buildGilbertVarshamovH n k
    print $ distance h
    putStrLn $ showM h
