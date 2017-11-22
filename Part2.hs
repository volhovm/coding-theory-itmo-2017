{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NoImplicitPrelude #-}
-- | Solutions for part 2

module Part2
    ( task7
    , task6
    , task215
    , task216
    ) where

import           Control.Lens    (at, ix, (?=))
import qualified Data.HashSet    as HS
import           Data.List       (delete, (!!), (\\))
import           Data.Map.Strict ((!))
import           Universum       hiding (transpose)
import           Unsafe          (unsafeHead)

-- Vertical vector
type BVector = [Bool]

showVec :: BVector -> String
showVec = map $ bool '0' '1'

showM :: [BVector] -> String
showM = intercalate "\n" . map showVec . transpose

-- | Produces a list of binary vectors of length n.
binaryVectors :: (Integral n) => n -> [BVector]
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
linearDependent vectors
    | any (== zero) vectors = True
    | otherwise = or $ map ((== zero) . sumAll) ps
  where
    n = length $ unsafeHead vectors
    zero = replicate n False
    sumAll :: [BVector] -> BVector
    sumAll = foldr sumBVectors (replicate (length $ unsafeHead vectors) False)
    ps :: [[BVector]]
    ps = allCombinations vectors

--distance :: [BVector] -> Integer
--distance matrix = fromMaybe 0 $ find hasDistance $ reverse [1..maxRank]
--  where
--    hasDistance :: Integer -> Bool
--    hasDistance i =
--        all (\c -> not (linearDependent c)) $ combinations i matrix
--    n = length (unsafeHead matrix)
--    k = length matrix
--    maxRank :: Integer
--    maxRank = toInteger $ min n k
--
--task21 :: Integer -> Integer -> ([BVector], Integer)
--task21 n k =
--    maximumBy (compare `on` snd) $ map (\m -> (m,distance m)) matrices
--  where
--    r = n - k
--    matrices = combinations n $ binaryVectors r

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

mMulM :: [BVector] -> [BVector] -> [BVector]
mMulM a b = transpose $ map (`vMulM` b) $ transpose a

isNullM :: [BVector] -> Bool
isNullM = all (all (== False))

testmmulm :: IO ()
testmmulm = do
    let g = map fromIntVector [[1,0],[0,1],[1,1]]
    let h = map fromIntVector [[1],[1],[1]]
    print $ map showVec $ g `mMulM` (transpose h)

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
    allEs = binaryVectors n

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
                 (binaryVectors n)
  where
    n = length h
    r = length (unsafeHead h)

-- | Given matrix H, returns (r,v1,v2) -- code radius r, vector v1
-- (not in code).
codeRadius :: [BVector] -> (Integer, BVector)
codeRadius h =
    maximumBy (comparing $ view _1) $
    map (\y -> (distToCodewords y, y))
        (binaryVectors n)
  where
    distToCodewords x = minimum $ map (dist x) codewords
    dist x y = weight $ x `sumBVectors` y
    codewords = codeH h
    n = length h

-- List of matrices
task21Hs :: [[BVector]]
task21Hs = map (map fromIntVector) [h1,h2,h3,h4,h5]
  where
    h1 = [[1,0,0,0,0],[0,1,0,0,0],[0,0,1,0,0],[0,0,0,1,0],[0,0,0,0,1],[1,1,1,1,1]]
    h2 = [[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1],[1,0,1,1],[1,1,0,1]]
    h3 = [[1,0,0],[0,1,0],[0,0,1],[1,1,0],[0,1,1],[1,0,1]]
    h4 = [[1,1],[1,0],[1,0],[1,0],[1,0],[1,0]]
    h5 = [[1],[1],[1],[1],[1],[1]]


task12 :: IO ()
task12 =
    forM_ task21Hs $ \h -> do
      print $ (map showVec) $ codeH h
      print $ (\(a,b) -> (a,showVec b)) $ codeRadius h

buildZeroNN :: [BVector] -> [BVector]
buildZeroNN h =
    traceShow (map showVec d0) $
    traceShow (map showVec $ solvingArea zero) $
    fromMaybe (error "should exist") $ find zCondition $ allCombinations $ codeH h
  where
--    kickWhilePossible $ delete zero $ codeH h
--  where
--    kickWhilePossible :: [BVector] -> [BVector]
--    kickWhilePossible zCandidate =
--        case find (\e -> zCondition $ delete e zCandidate) zCandidate of
--            Just x  -> kickWhilePossible (delete x zCandidate)
--            Nothing -> zCandidate
    zCondition :: [BVector] -> Bool
    zCondition zCandidate =
        let union = HS.fromList $ concat $ map solvingArea zCandidate
        in all (`HS.member` union) d0

    n = length h

    zero = replicate n False
    d0 = neighborhood $ solvingArea zero

    solvingArea :: BVector -> [BVector]
    solvingArea a = filter ((== a) . decode) $ binaryVectors n

    -- decoding
    syndromMap = syndromDecodeBuild h
    decode :: BVector -> BVector
    decode y = do
        let syndrom = y `vMulM` transpose h
        let e = syndromMap ! syndrom
        y `sumBVectors` e

    -- Calculates closest neighborhood by solving area
    neighborhood :: [BVector] -> [BVector]
    neighborhood sA = filter (\x -> x `notElem` sA && invertedIn x)
                              (binaryVectors (length $ unsafeHead sA))
      where
        invertedIn x =
            let invertedSet =
                    mapMaybe (\i -> if x !! i then Just (x & ix i .~ False) else Nothing)
                             [0..length x-1]
            in any (`elem` sA) invertedSet

-- | You pass code, y, it returns c.
decodeZeroNN :: [BVector] -> BVector -> BVector
decodeZeroNN h x0 = go (zero,x0)
  where
    go (c,x) =
        case find (\v -> weight (x `sumBVectors` v) < weight x) zNN of
            Nothing -> c
            Just v  -> go (c `sumBVectors` v, x `sumBVectors` v)

    zero = replicate (length h) False
    zNN = buildZeroNN h

task215 :: IO ()
task215 =
    forM_ task21Hs $ \h -> do
        print $ (map showVec) $ codeH h
        putText "~~~~~~~~~~~~~~~~~~~~~"
        print $ map showVec $ buildZeroNN h
        putText "---------------------"

findGfromH :: [BVector] -> [BVector]
findGfromH h =
    fromMaybe (error "can't happen2") $
    find (\g -> formsBasis g && givesNull g) allPossibleG
  where
    formsBasis g = not $ linearDependent $ transpose g
    givesNull g = isNullM $ g `mMulM` transpose h

    allPossibleG = combinations (fromIntegral n) $ binaryVectors k
    n = length h
    r = length $ unsafeHead h
    k = n - r

hamming74H = drop 1 $ binaryVectors 3
hamming74G = findGfromH hamming74H
hammingE84H = map (++ [True]) $ binaryVectors 3
hammingE84G = findGfromH hammingE84H

task216 :: IO ()
task216 = do
    let rankk k x = length $ filter (not . linearDependent) $ combinations k x
    putStrLn $ showM hamming74H
    putText "---"
    putStrLn $ showM hamming74G
    print $ rankk 4 hamming74G
    print $ length $ combinations 4 [1..7]
    putStrLn $ showM hammingE84H
    putText "---"
    putStrLn $ showM hammingE84G
    print $ rankk 4 hammingE84G
    print $ length $ combinations 4 [1..8]
