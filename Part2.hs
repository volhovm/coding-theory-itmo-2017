{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NoImplicitPrelude #-}
-- | Solutions for part 2

module Part2 (task21) where

import           Data.Choose
import           Universum
import           Unsafe      (unsafeHead)

type BVector = [Bool]

-- | Produces a list of binary vectors of length n.
binaryVectors :: Integer -> [BVector]
binaryVectors = binGen
  where
    binGen 0 = [[]]
    binGen n =
        let x = binGen (n-1)
        in map (False :) x <> map (True :) x

sumBVectors :: BVector -> BVector -> BVector
sumBVectors = zipWith s
  where
    s False False = False
    s True True   = False
    s _ _         = True

combinations :: Integer -> [a] -> [[a]]
combinations 0 _  = return []
combinations n xs = do y:xs' <- tails xs
                       ys <- combinations (n-1) xs'
                       return (y:ys)

allCombinations :: [a] -> [[a]]
allCombinations xs = concatMap (flip combinations xs) [1..(toInteger $ length xs)]

linearDependent :: [BVector] -> Bool
linearDependent [] = False
linearDependent vectors = or cases
  where
    cases :: [Bool]
    cases = do
        c <- ps
        let cases2 :: [BVector] -> [Bool]
            cases2 es = do
                x <- [0..(length es-1)]
                let part1 = take x es
                let e = unsafeHead $ drop x es
                let part2 = drop (x+1) es
                let other = part1 <> part2
                pure $ sumAll other == e
        pure $ or (cases2 c)
    sumAll :: [BVector] -> BVector
    sumAll = foldr sumBVectors (replicate (length $ unsafeHead vectors) False)
    ps :: [[BVector]]
    ps = allCombinations vectors

distance :: [BVector] -> Integer
distance matrix = fromMaybe 0 $ find hasDistance $ reverse [1..maxRank]
  where
    hasDistance :: Integer -> Bool
    hasDistance i =
        all (\c -> not (linearDependent c)) $ combinations i matrix
    n = length (unsafeHead matrix)
    k = length matrix
    maxRank :: Integer
    maxRank = toInteger $ min n k

task21 :: Integer -> Integer -> ([BVector], Integer)
task21 n k =
    traceShow matrices $
    maximumBy (compare `on` snd) $ map (\m ->
                                          trace ("Calculating dist for " <> show m :: Text) $
                                          (m,distance m)) matrices
  where
    r = n - k
    matrices = combinations n $ binaryVectors r
