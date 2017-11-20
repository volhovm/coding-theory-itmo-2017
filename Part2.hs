{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NoImplicitPrelude #-}
-- | Solutions for part 2

module Part2
    ( task21
    , task7
    , task6
    ) where

import           Control.Lens (at, (?=))
import           Data.Choose  hiding (at)
import           Data.List    ((!!))
import qualified Data.Map     as M
import           Universum    hiding (transpose)
import           Unsafe       (unsafeHead)

-- Vertical vector
type BVector = [Bool]

showVec :: BVector -> String
showVec = map $ bool '0' '1'

-- | Produces a list of binary vectors of length n.
binaryVectors :: Integer -> [BVector]
binaryVectors = binGen
  where
    binGen 0 = [[]]
    binGen n =
        let x = binGen (n-1)
        in map (False :) x <> map (True :) x

fromIntVector :: [Integer] -> [Bool]
fromIntVector = map toBool
  where
    toBool 1 = True
    toBool 0 = False
    toBool e = error $ "fromIntVector: " <> show e

sumBVectors :: BVector -> BVector -> BVector
sumBVectors = zipWith s
  where
    s False False = False
    s True True   = False
    s _ _         = True

mulBVectors :: BVector -> BVector -> BVector
mulBVectors = zipWith s
  where
    s False _   = False
    s _ False   = False
    s True True = True


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
    maximumBy (compare `on` snd) $ map (\m -> (m,distance m)) matrices
  where
    r = n - k
    matrices = combinations n $ binaryVectors r

weight :: BVector -> Integer
weight = sum . map (bool 0 1)

scalar :: BVector -> BVector -> Bool
scalar a b =
    case weight (a `mulBVectors` b) `mod` 2 of
       1 -> True
       _ -> False

transpose :: [[a]] -> [[a]]
transpose m1 = [map (!! i) m1 | i <- [0..(n-1)] ]
  where
    n = length (unsafeHead m1)

vMulM :: BVector -> [BVector] -> BVector
vMulM v m = map (scalar v) m

syndromDecodeBuild :: [BVector] -> Map BVector BVector
syndromDecodeBuild h = flip execState mempty $ forM_ allEs $ \e -> do
    let syndrom = e `vMulM` (transpose h)
    let updateSyndrom = at syndrom ?= e
    use (at syndrom) >>= \case
        Just x  -> when (weight x > weight e) updateSyndrom
        Nothing -> updateSyndrom
  where
    n = length h
    allEs :: [BVector]
    allEs = binaryVectors (fromIntegral n)

task7 :: Map BVector BVector
task7 = syndromDecodeBuild h
  where
    h = map fromIntVector $
        [ [1,1,1,0]
        , [1,1,1,1]
        , [1,0,0,1]
        , [0,1,1,1]
        , [1,1,0,1]
        , [1,0,1,0]
        , [1,0,0,0]
        , [1,1,1,1]
        , [0,1,0,1]
        , [0,0,1,1] ]

task6 :: Map BVector BVector
task6 = syndromDecodeBuild h
  where
    h = drop 1 $ binaryVectors 3

-- | Returns complete list of code vectors by H.
codeH :: [BVector] -> [BVector]
codeH h = filter (\y -> y `vMulM` (transpose h) == replicate r False)
                 (binaryVectors (fromIntegral n))
  where
    n = length h
    r = length (unsafeHead h)

codeRadius :: [BVector] -> (Integer, BVector, BVector)
codeRadius h =
    maximumBy (comparing $ view _1) $
    map (\y -> let d = decode y in (weight (decode y `sumBVectors` y), y, d))
        (binaryVectors $ fromIntegral n)
  where
    decode :: BVector -> BVector
    decode y = do
        let syndrom = y `vMulM` transpose h
        let err = fromMaybe (error "can't happen") $ M.lookup syndrom decodeMap
        y `sumBVectors` err
    decodeMap = syndromDecodeBuild h
    n = length h

task12 :: IO ()
task12 = do
    print $ map showVec $ codeH h
    print $ (\(a,b,c) -> (a,showVec b,showVec c)) $ codeRadius h
  where
    h = map fromIntVector $
        [ [1,1,1,0]
        , [1,1,1,1]
        , [1,0,0,1]
        , [0,1,1,1]
        , [1,1,0,1]
        , [1,0,1,0]
        , [1,0,0,0]
        , [1,1,1,1]
        , [0,1,0,1]
        , [0,0,1,1] ]
