{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}

-- | Coding theory solutions.

module Lib
    ( task27
    , task26
    , task215
    , task216
    , findDRange
    , buildGilbertVarshamovH
    , distance
    , showM
    , task42
    ) where


import qualified Prelude
import Universum hiding (head, last, transpose, (<*>))

import Control.Lens (at, ix, (?=))
import qualified Data.HashSet as HS
import Data.List (findIndex, head, last, nub, (!!))
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as M
import GHC.Conc (par)
import Graphics.EasyPlot
import System.IO.Unsafe (unsafePerformIO)
import System.Random

import Fields

----------------------------------------------------------------------------
-- Utilities
----------------------------------------------------------------------------

randomGaussian :: (Floating a, Random a) => a -> a -> IO a
randomGaussian mean sigma = do
    [u1,u2] <- replicateM 2 $ randomRIO (0,1)
    let r = sqrt (-2 * log u1)
    let t = 2 * pi * u2
    let x = r * cos t
    pure $ x * sigma + mean

randomNormal :: (Floating a, Random a) => IO a
randomNormal = randomGaussian 0 1

-- Vertical vector
type BVector = [Bool]

-- row dominated matrix
type BMatrix = [BVector]

showVec :: BVector -> String
showVec = map $ bool '0' '1'

showM :: BMatrix -> String
showM = intercalate "\n" . map showVec . transpose

fromStrVec :: String -> BVector
fromStrVec = map go
  where go '0' = False
        go '1' = True
        go _   = error "fromStrVec"

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

combinationsN :: Integer -> Integer -> Integer
combinationsN n k = (fact n) `div` (fact k) `div` (fact $ n - k)
  where
    fact (x :: Integer) = product [1..x]


allCombinations :: [a] -> [[a]]
allCombinations xs = concatMap (flip combinations xs) [1..(toInteger $ length xs)]

log2 :: Floating a => a -> a
log2 x = log x / log 2

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
    n = length (head m1)

vMulM :: BVector -> BMatrix -> BVector
vMulM v m =
    if length v /= length m
    then error "vMulM dimensions"
    else map (scalar v) (transpose m)

mMulM :: BMatrix -> BMatrix -> BMatrix
mMulM a b =
    if length (head a) /= length b
    then error $ "mMulM dimensions: " <> show (length (head a), length b)
    else transpose $ map (`vMulM` b) a

isNullM :: BMatrix -> Bool
isNullM = all (all (== False))

----------------------------------------------------------------------------
-- Part 2
----------------------------------------------------------------------------


-- | Checks if any combination of weight <= d are linear dependent.
linearDependentSubset :: Integer -> [BVector] -> Bool
linearDependentSubset _ [] = False
linearDependentSubset d vectors
    | any (== zero) vectors = True
    | otherwise = or $ map ((== zero) . sumAll) ps
  where
    n = length $ head vectors
    zero = replicate n False
    sumAll :: [BVector] -> BVector
    sumAll = foldr sumBVectors $ replicate (length $ head vectors) False
    ps :: [[BVector]]
    ps = concatMap (flip combinations vectors) [1..(min d (fromIntegral $ length vectors))]


-- | Checks if any combination of given vectors can be linear dependent.
linearDependent :: [BVector] -> Bool
linearDependent vectors =
    linearDependentSubset (fromIntegral $ length vectors) vectors

-- | Returns any linearly independent subset of vectors passed.
linearReduce :: [BVector] -> [BVector]
linearReduce = foldl' gather []
  where
    gather acc x = let acc' = acc++[x]
                   in if linearDependentSubset (fromIntegral $ length acc') acc'
                      then acc
                      else acc'

distance :: [BVector] -> Integer
distance matrix =
    (+1) $ fromMaybe 0 $ find hasDistance $ reverse [1..maxRank]
  where
    hasDistance :: Integer -> Bool
    hasDistance i = not (linearDependentSubset i matrix)
    n = length (head matrix)
    k = length matrix
    maxRank :: Integer
    maxRank = toInteger $ min n k

encodeG :: BMatrix -> BVector -> BVector
encodeG g x = x `vMulM` g

syndromDecodeBuild :: [BVector] -> Map BVector BVector
syndromDecodeBuild h = flip execState mempty $ forM_ allEs $ \e -> do
    let syndrom = e `vMulM` h
    let updateSyndrom = at syndrom ?= e
    use (at syndrom) >>= \case
        Just x  -> when (weight x > weight e) updateSyndrom
        Nothing -> updateSyndrom
  where
    n = length h
    allEs :: [BVector]
    allEs = binaryVectors n

task27 :: Map BVector BVector
task27 = syndromDecodeBuild h23

task26 :: Map BVector BVector
task26 = syndromDecodeBuild h
  where
    h = drop 1 $ binaryVectors (3::Int)

-- | Returns complete list of code vectors by H.
codeH :: [BVector] -> [BVector]
codeH h = filter (\y -> y `vMulM` h == replicate r False)
                 (binaryVectors n)
  where
    n = length h
    r = length (head h)

-- | Get all code words from G.
codeG :: [BVector] -> [BVector]
codeG g = map (encodeG g) $ binaryVectors k
  where
    k = length g

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
--    traceShow (map showVec d0) $
--    traceShow (map showVec $ solvingArea zero) $
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
        let syndrom = y `vMulM` h
        let e = syndromMap ! syndrom
        y `sumBVectors` e

    -- Calculates closest neighborhood by solving area
    neighborhood :: [BVector] -> [BVector]
    neighborhood sA = filter (\x -> x `notElem` sA && invertedIn x)
                              (binaryVectors (length $ head sA))
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

-- | Checks if g and h are compatible.
checkGH :: BMatrix -> BMatrix -> Bool
checkGH g h = isNullM $ g `mMulM` transpose h

---- | Finds g given h.
--findGfromH :: [BVector] -> [BVector]
--findGfromH h =
--    fromMaybe (error "can't happen2") $
--    find (\g -> formsBasis g && checkGH g h) allPossibleG
--  where
--    formsBasis g = not $ linearDependent $ transpose g
--
--    allPossibleG = combinations (fromIntegral n) $ binaryVectors k
--    n = length h
--    r = length $ head h
--    k = n - r

boolToZ = map (map (bool (Z 0) (Z 1)))
zToBool = let x (Z 0) = False
              x (Z 1) = True
          in map (map x)

gToHGauss :: BMatrix -> BMatrix
gToHGauss (boolToZ -> (g :: [[Z 2]])) =
    let (gk, gn) = msize (Matrix g)
        g' = unMatrix $ gaussSolve $ Matrix g
        p = map (drop gk) g'
        r = gn - gk
        zeroes i = replicate (fromIntegral i) f0
        h = map (\(row,i) -> row <> zeroes i <> [f1] <> zeroes (r-i-1))
                (transpose p `zip` [0..])
    in zToBool h

hToGGauss :: BMatrix -> BMatrix
hToGGauss (boolToZ -> (h :: [[Z 2]])) =
    let (hr, hn) = msize (Matrix h)
        h' = map (\r -> drop (fromIntegral $ hn-hr) r <> take (fromIntegral $ hn-hr) r) h
        h'' = unMatrix $ gaussSolve $ Matrix h'
        p = map (drop hr) h''
        k = hn - hr
        zeroes i = replicate (fromIntegral i) f0
        g = map (\(row,i) -> zeroes i <> [f1] <> zeroes (k-i-1) <> row)
                (transpose p `zip` [0..])
    in zToBool g

hamming74H = transpose $ drop 1 $ binaryVectors (3 :: Int)
hamming74G = hToGGauss hamming74H
hammingE84H = transpose $ map (++ [True]) $ binaryVectors (3 :: Int)
hammingE84G = hToGGauss hammingE84H

task216 :: IO ()
task216 = do
    let rankk k x = length $ filter (not . linearDependent) $ combinations k x
    putStrLn $ showM hamming74H
    putText "---"
    putStrLn $ showM hamming74G
    print $ rankk 4 hamming74G
    print $ combinationsN 7 4
    putStrLn $ showM hammingE84H
    putText "---"
    putStrLn $ showM hammingE84G
    print $ rankk 4 hammingE84G
    print $ combinationsN 8 4

-- | Chapter 2 task 3 - individual task matrix G.
g23 :: BMatrix
g23 =
    transpose $
    map fromIntVector $
    [ [1, 0, 0, 0, 0, 0]
    , [0, 1, 0, 0, 0, 0]
    , [0, 0, 1, 0, 0, 0]
    , [0, 0, 0, 1, 0, 0]
    , [0, 0, 0, 0, 1, 0]
    , [0, 0, 0, 0, 0, 1]
    , [1, 1, 1, 0, 1, 1]
    , [1, 1, 0, 1, 1, 0]
    , [1, 1, 0, 1, 0, 1]
    , [0, 1, 1, 1, 1, 0]
    ]

-- | Dual H matrix.
h23 :: BMatrix
h23 =
    transpose $
    map fromIntVector $
    [ [1, 1, 1, 0]
    , [1, 1, 1, 1]
    , [1, 0, 0, 1]
    , [0, 1, 1, 1]
    , [1, 1, 0, 1]
    , [1, 0, 1, 0]
    , [1, 0, 0, 0]
    , [0, 1, 0, 0]
    , [0, 0, 1, 0]
    , [0, 0, 0, 1]
    ]

g23Dimq :: BMatrix
g23Dimq =
    map fromIntVector $
    [ [1, 0, 0, 0, 0, 0, 1, 1, 1, 1]
    , [0, 1, 0, 0, 0, 0, 1, 1, 1, 0]
    , [0, 0, 1, 0, 0, 0, 0, 1, 0, 1]
    , [0, 0, 0, 1, 0, 0, 0, 1, 1, 0]
    , [0, 0, 0, 0, 1, 0, 1, 1, 0, 0]
    , [0, 0, 0, 0, 0, 1, 1, 0, 1, 0]
    ]

h23Dimq :: BMatrix
h23Dimq =
    map fromIntVector $
    [ [1, 1, 0, 0, 1, 1, 1, 0, 0, 0]
    , [1, 1, 1, 1, 1, 0, 0, 1, 0, 0]
    , [1, 1, 0, 1, 0, 1, 0, 0, 1, 0]
    , [1, 0, 1, 0, 0, 0, 0, 0, 0, 1]
    ]

_testGH :: IO ()
_testGH = do
    print $ checkGH g23 h23
    let h' = gToHGauss g23
    print $ checkGH g23 h'
    let g' = hToGGauss h23Dimq
    print $ checkGH g' h23Dimq
    print $ checkGH g23Dimq h23Dimq

----------------------------------------------------------------------------
-- Part 3
----------------------------------------------------------------------------

findDRange :: Integer -> Integer -> (Integer,Integer)
findDRange n k = (lastB hammingCond [1..n], lastB gilbertVarshamovCond [1..n])
  where
    lastB cond = last . takeWhile cond
    cast :: (Integral a, Num b) => a -> b
    cast = fromIntegral
    hammingCond :: Integer -> Bool
    hammingCond d =
        let t = (d - 1) `div` 2
        in (2.0^k::Double) <= ((2.0^n) / (cast (sum $ map (combinationsN n) [0..t]) :: Double))
    gilbertVarshamovCond :: Integer -> Bool
    gilbertVarshamovCond d = 2^(n-k) > (sum $ map (combinationsN $ n -1) [0..(d-2)])


buildGilbertVarshamovH :: Integer -> Integer -> [BVector]
buildGilbertVarshamovH n k = genVectors (n-1) [initVec]
  where
    genVectors 0 acc = acc
    genVectors l acc =
        let a = fromMaybe (error "couldn't find one") $
                find (\x -> not $ linearDependentSubset (d-1) (x:acc)) (binaryVectors r)
        in genVectors (l-1) (a:acc)

    d = snd $ findDRange n k
    r = n - k
    -- Vector 00..01 of length r
    initVec = True : replicate (fromIntegral $ r-1) False

illustrateGVH :: IO ()
illustrateGVH = do
    void $ plot (PNG "kek.png")
        [ Function2D [Title "Hamming"] [Range (1::Double) 22]
          (\(round -> k) -> fst $ findDRange (2*k) k)
        , Function2D [Title "Gilbert-Varshamov"] [Range 1 22]
          (\(round -> k) -> snd $ findDRange (2*k) k)
        , Data2D [Title "Best known"] [] realData
        ]
  where
    realData = [(4,4),(5,4),(6,4),(7,4),(8,5),(9,6),(10,6),(11,7),(12,8), (13,7),(14,8),(15,8),(16,8),(17,8),(18,8),(19,9),(20,10)]

----------------------------------------------------------------------------
-- Part 4
----------------------------------------------------------------------------

-- | Channel is function from (c,y) to probability p.
type Channel = Bool -> Double -> Double

type Encoder = Bool -> IO Double
type Decoder = [Double] -> BVector

-- | Discrete stationary channel.
dsc :: Double -> Channel
dsc ε = curry $ \case
    (False, 0) -> 1 - ε
    (True,  1) -> 1 - ε
    (False, 1) -> ε
    (True,  0) -> ε
    _          -> error "dsc is invalid"

dscEncode :: Double -> Bool -> IO Double
dscEncode ε b = do
    r <- randomRIO (0,1)
    pure $ case bool b (not b) $ r < ε of
      False -> 0
      True  -> 1

-- | Additive white gaussian noise.
awgn :: Double -> Double -> Channel
awgn n0 e =
    \c y ->
      let μ = (bool (-) (+) c) 0 (sqrt e)
          σ2 = n0 / 2
      in gaussian μ σ2 y
  where
    gaussian :: Double -> Double -> Double -> Double
    gaussian μ σ2 x = exp (- ((x - μ)**2)/(2*σ2)) / (sqrt (2 * pi * σ2))

awgnEncode :: Double -> Double -> Bool -> IO Double
awgnEncode n0 e v0 = do
    let se = sqrt e
    let v = bool (-se) se v0
    randomGaussian v (n0/2)

-- | Maximum likelihood decoder.
decodeML :: Channel -> [BVector] -> [Double] -> BVector
decodeML chan codeWords y =
    fst $ maximumBy (comparing snd) $
    map (\c -> (c,aPrioriProb c)) codeWords
  where
    aPrioriProb c = product $ map (uncurry chan) $ c `zip` y

-- | Maximum a posterior probability decoder.
decodeMaxAp :: Channel -> [BVector] -> [Double] -> BVector
decodeMaxAp chan codeWords y =
    fst $ maximumBy (comparing snd) pcy
  where
    -- p(c|y)
    pcy = map (\c -> (c,pycMap M.! c * pc / py)) codeWords

    -- map c -> p(y|c)
    computePyc :: BVector -> Double
    computePyc c = product $ map (uncurry chan) $ c `zip` y
    pycMap = M.fromList $ map (\c -> (c,computePyc c)) codeWords

    -- p(y)
    py = sum $ map (\c -> pycMap M.! c * pc) codeWords

    -- p(c)
    pc = 1/(fromIntegral $ length codeWords)

erf :: Double -> Double
erf x = sign*y
  where
    a1 =  0.254829592
    a2 = -0.284496736
    a3 =  1.421413741
    a4 = -1.453152027
    a5 =  1.061405429
    p  =  0.3275911

    -- Abramowitz and Stegun formula 7.1.26
    sign = if x > 0
               then  1
               else -1
    t  =  1.0/(1.0 + p* abs x)
    y  =  1.0 - (((((a5*t + a4)*t) + a3)*t + a2)*t + a1)*t*exp(-x*x)

calcp :: Double -> Double
calcp en0 =
    let qfunc x = 1 - 0.5 * (erf (x / sqrt 2) + 1)
    in qfunc (sqrt (2 * en0))

task42 :: Integer -> IO ()
task42 i = do
    let g = h23Dimq
    let n :: Integer
        n = fromIntegral $ length g23
    let log10 x = log x / log 10
    let code = codeG g
    let diffV x y = weight $ x `sumBVectors` y
    rVecsVar <-
        newIORef =<<
        map (code !!) <$> replicateM (fromInteger i) (randomRIO (0,length code - 1))
    let funcGen :: Encoder -> Decoder -> Decoder -> (Double,Double)
        funcGen encoder decoder1 decoder2 = unsafePerformIO $ fmap force $ do
            (rVecsEnc :: [(BVector,[Double])]) <-
                readIORef rVecsVar >>= \rVecs ->
                forM rVecs (\r -> (r,) <$> mapM encoder r)
            let calcRes dc =
                    sum (map (\(a,b) -> fromIntegral $ dc b `diffV` a) rVecsEnc) /
                    fromIntegral (i * n)
            let r1 = force $ calcRes decoder1
            let r2 = force $ calcRes decoder2
            pure $ r1 `par` r2 `par` (r1,r2)
    let fromdecibels :: Double -> Double
        fromdecibels x = 10 ** (x / 10)
    let dscDo (fromdecibels -> en0) =
            let e = (calcp en0)
            in funcGen (dscEncode e)
                       (decodeML (dsc e) code)
                       (decodeMaxAp (dsc e) code)
    let awgnDo (fromdecibels -> en0) =
            let e = 5
                n0 = e / en0
            in funcGen (awgnEncode n0 e) (decodeML (awgn n0 e) code)
                                         (decodeMaxAp (awgn n0 e) code)
    let f2d (t,f) = Data2D [Title t, Style Lines] [] f
    let yToLog (x,y) = (x,log10 y)
    let frange1 = [-2..4]++[4.5,4.7..8.5]
    let frange2 = [-2..4]++[4.1,4.2..4.9]

    (datasets :: [(String,[(Double,Double)])]) <-
        map (second (map yToLog)) . concat <$>
        mapM
        (\(t,f,rng) -> do
              putStrLn $ "Evaluating " <> t
              points <-
                  mapM (\x -> do putStrLn $ "calculating " <> t <> " in " <> show x
                                 res <- pure $ force $ f x
                                 putText $ "res is : " <> show res
                                 pure $ force $ (x, res)) rng
              let points1 = map (second fst) points
              let points2 = map (second snd) points
              !ret <- pure $ force $ [(t <> ", ML",points1), (t <> ", MAP",points2)]
              putStrLn $ "Evaluated " <> t
              pure ret)
        [ ("DSC", dscDo, frange1), ("AWGN", awgnDo, frange2) ]
    putText "mda"
    print datasets
    void $ plot (SVG "task42PlotDimqTemp.svg") $ map f2d datasets


type Lattice v e = [[(v, Map Int e)]]
type CodeLattice = Lattice () Bool
type SyndromLattice = Lattice BVector Bool


showSyndromeLattice :: SyndromLattice -> Text
showSyndromeLattice x = unlines $ map (show . map (\(v,m) -> (showVec v,M.toList m))) x

buildSyndromLattice :: BMatrix -> SyndromLattice
buildSyndromLattice h =
    pruneForks $ rawLattice 0 [[(zSyndrome, mempty)]]
    --reverse $ rawLattice 0 [[(zSyndrome, mempty)]]
  where
    n = length h
    r = length $ head h
    zSyndrome = replicate r False

    -- From two lists, creates function a -> i which tells that element a
    -- now has index i, or it was removed if key not present.
    createMods :: (Ord a) => [a] -> [a] -> Map Int Int
    createMods before after =
        M.fromList $
        mapMaybe (\(b,i) -> (i,) <$> findIndex (== b) after) (before`zip`[0..])

    -- Work on reversed lattice
    deleteFork (top:xs) mods =
        let fixEdge :: (Int,Bool) -> Maybe (Int,Bool)
            fixEdge (i,b) = (,b) <$> M.lookup i mods
            edgesFixed = map (\(e,v) -> (e,M.fromList $ mapMaybe fixEdge $ M.toList v)) top
            newTop = filter (not . M.null . snd) edgesFixed
            newMods = createMods (map fst top) (map fst newTop)
        in newTop:(deleteFork xs newMods)
    deleteFork _ _ = []

    pruneForks :: SyndromLattice -> SyndromLattice
    pruneForks (top:xs) =
        let newTop = [(zSyndrome, mempty)]
            mods = createMods (map fst top) [zSyndrome]
        in reverse $ newTop:(deleteFork xs mods)
    pruneForks _ = error "pruneForks"

    -- Returns reversed lattice
    rawLattice :: Int -> SyndromLattice -> SyndromLattice
    rawLattice step acc | step >= n = acc
    rawLattice step (top:t) = do
        let buildNext syndrom0 b = syndrom0 `sumBVectors` (map (&& b) (h !! step))
        let processed = map (\(v,_) -> let s1 = buildNext v True
                                           s2 = buildNext v False
                                       in ((v,[(True,s1),(False,s2)]),[s1,s2])) top
        let allNewStates = sort $ ordNub $ concatMap snd processed
        let resolveRefs :: [(Bool,BVector)] -> Map Int Bool
            resolveRefs =
                M.fromList .
                map (\(b,sref) -> (fromMaybe (error "a") $ findIndex (==sref) allNewStates,b))
        let newTop = map (second resolveRefs . fst) processed
        let newLayer = map (,mempty) allNewStates
        rawLattice (step + 1) (newLayer:newTop:t)
    rawLattice _ _ = error "rawLattice"

task44 :: IO ()
task44 = do
    -- test from textbook
    -- putText $ showSyndromeLattice $ buildSyndromLattice $ map fromIntVector $ [[1,0,0],[1,0,1],[0,1,0],[0,0,1],[1,1,0],[1,1,1]]
    putText $ showSyndromeLattice $ buildSyndromLattice $ h23

----------------------------------------------------------------------------
-- 7.1 LROS
----------------------------------------------------------------------------

-- | ЛРОС generator, first list is Λ_i, second list is S_i (initial).
data LrosGen = LrosGen BVector BVector deriving Eq

instance Show LrosGen where
    show (LrosGen a b) = "LrosGen " <> showVec a <> " " <> showVec b

emulateLros :: LrosGen -> [Bool]
emulateLros (LrosGen coeffs st) = do
    let curOut = last st
    let pr = scalar coeffs st
    let newst = take (length st) $ pr : st
    curOut : emulateLros (LrosGen coeffs newst)

genLros :: Integer -> BVector -> [LrosGen]
genLros n v | n > (fromIntegral $ length v) = error "genLros: you don't want that, use naive lros"
genLros n v = [LrosGen y initState | y <- binaryVectors n]
  where
    initState = reverse $ take (fromIntegral n) v

findLros :: BVector -> IO LrosGen
findLros vec = do
    go 2
  where
    go n | n > (fromIntegral $ length vec) = error "There always exists naive lros"
         | otherwise = do
              putText $ "Iterating for " <> show n
              maybe (go $ n+1) pure $
                  find (\lr -> vec `isPrefixOf` emulateLros lr) $ genLros n vec

task71 :: IO ()
task71 = do
    s <- findLros $ fromStrVec "010011000111"
    print s
    putStrLn $ showVec $ take 22 $ emulateLros s

----------------------------------------------------------------------------
-- 7.6 BCH
----------------------------------------------------------------------------

{-
Great presentation on bch codes:
https://web.stanford.edu/class/ee387/handouts/notes19.pdf
-}


cyclotomicClasses :: forall a . (Eq a,Field a) => [[Integer]]
cyclotomicClasses = sort $ go [[0]] 0
  where
    go :: [[Integer]] -> Integer -> [[Integer]]
    go s gi | gi >= fsize - 1 = s
    go s gi =
        let newX :: [Integer]
            newX = gi : takeWhile (/= gi) (iterate (\i -> i * 2 `mod` (fsize - 1)) (gi*2))
        in if gi `elem` (concat s)
           then go s (gi+1)
           else go (map (`mod` (fsize - 1)) newX:s) (gi+1)
    fsize = getFieldSize (Proxy @a)

-- | First argument -- list of cyclotomic classes and desired
-- d. Return value is cyclotomic classes that create the match. It
-- returns the minumum number of classes required to match.
matchCyclotomic :: [[Integer]] -> Integer -> ([[Integer]], (Integer,Integer))
matchCyclotomic classes (fromIntegral -> d) =
    head $
    mapMaybe (\comb -> (comb,) <$> toMatchSimple (ordNub $ concat comb)) $
    allCombinations classes
  where
    -- PGZ is only explained when consequent cyclotomic powers are [0..d],
    -- so b = 0. So this is a simplified version of toMatch.
    --
    -- In other words, we only consider narrow-sense BCH codes
    toMatchSimple :: [Integer] -> Maybe (Integer, Integer)
    toMatchSimple (sort -> l) =
        let l' = take (d-1) l
        in if l' `isPrefixOf` [1..] && (length l' == d-1)
        then Just (1, fromIntegral d-1) else Nothing

     -- Tries to find d-1 consequent elems in the list
    _toMatch :: [Integer] -> Maybe (Integer, Integer)
    _toMatch (sort -> l) =
        let f [] i       = [i]
            f xs@(x:_) i | i == x + 1 = i:xs
                         | length xs >= (d - 1) = xs
                         | otherwise  = [i]
            res = reverse $ foldl' f [] l
        in guard (length res >= (d-1)) >> pure (head res, last res)

minFromCyclotomic ::
       forall p n. (KnownNat n, PrimePoly p n)
    => [Integer]
    -> Poly (FinPoly p (Z n))
minFromCyclotomic ccl =
    let foo i = let y = Poly [g <^> i]
                in x <-> y
                  -- if g' == x && i == 1
                  -- then Poly g'
                  -- else x <-> Poly [g <^> i] -- FIXME g^i should be in smaller field?
    in foldr1 (<*>) $ map foo ccl
  where
    x = Poly [mkFinPoly (Poly [1]), f0]
    g = getGen @(FinPoly p (Z n))

type MishFinPoly = FinPoly 67 (Z 2)

data BCHParams (p :: Nat) (n :: Nat) = BCHParams
    { bchMs         :: [Poly (FinPoly p (Z n))]
    , bchPoly       :: Poly (FinPoly p (Z n))
    , bchPows       :: (Integer, Integer)
    , bchD          :: Integer
    -- Extra info:
    , bchCyclotomic :: [[Integer]]
    } deriving Show


data BCHCode (p :: Nat) = BCHCode
    { bchN      :: Integer
    , bchK      :: Integer
    , bchParams :: BCHParams p 2
    , bchg      :: Poly (Z 2)
      -- ^ Generator polynomial
    , bchG      :: Matrix (Z 2)
    , bchH      :: Matrix (Z 2)
    } deriving Show


-- | Finds minimal polynomials forming BCH generator.
buildBCH :: forall p n . PrimePoly p n => Integer -> BCHParams p n
buildBCH d =
    let ccl = cyclotomicClasses @(FinPoly p (Z n))
        (bchCyclotomic, bchPows) = matchCyclotomic ccl d
        bchMs = map (minFromCyclotomic @p @n) bchCyclotomic
        bchPoly = foldl1 (<*>) $ nub bchMs
        bchD = d
    in BCHParams{..}

-- | Encoding in cyclic codes is just multiplying by generator.
bchEncode :: KnownNat n => Poly (Z n) -> [Z n] -> Poly (Z n)
bchEncode g m = g <*> (Poly $ reverse m)

-- | Creates generator matrix from cyclic code generator polynomial.
cyclicToG :: (Integral i) => i -> BVector -> BMatrix
cyclicToG (fromIntegral -> n) g =
    transpose $ map (\i -> pz i ++ g ++ pz (k-i-1)) [0..(k-1)]
  where
    -- paste zeroes
    pz i = replicate i False
    r = length g - 1
    k = n - r

paramsToCode :: forall p. (PrimePoly p 2) => BCHParams p 2 -> Integer -> BCHCode p
paramsToCode bchParams@BCHParams{..} bchN =
    traceShow bchH $
    BCHCode{..}
  where
    pContent = reverse $ unPoly bchPoly
    l :: Integer
    l = fromIntegral $ length pContent
    bchK = bchN - l + 1
    α = getGen @(FinPoly p (Z 2))
    hoistg :: Poly (FinPoly p (Z 2)) -> Poly (Z 2)
    hoistg (Poly els) =
        let hoistFunc :: FinPoly p (Z 2) -> Z 2
            hoistFunc (FinPoly (Poly [e])) = e
            hoistFunc _                    = error "hoistg"
        in Poly $ map hoistFunc els
    bchg = hoistg bchPoly
    -- H is built as on page 176 formula 6.8
    bchH =
        Matrix $
        boolToZ $ linearReduce $ zToBool $
        -- transforms list of coefficients to N lists of coefficients
        -- of sublists
        --
        -- e.g. [α^1, α^2, α^4] will turn into
        -- [ [α^1_1, α^2_1, α^4_1]
        -- , [α^1_2, α^2_2, α^4_2]
        -- , ... to power 4 if we work in finite field modulo poly degree 5
        let expandPowers :: [FinPoly p (Z 2)] -> [[(Z 2)]]
            expandPowers =
                transpose .
                map (\(FinPoly (Poly x)) ->
                       let s = reverse x
                           fieldM = length (unPoly $ reflectCoeffPoly @p @2) - 1
                       in s <> replicate (fieldM - length s) f0)
        in concatMap (\(b0:_) -> expandPowers $ map ((α <^> b0) <^>) [0..bchN-1])
                     bchCyclotomic

    bchG =
        let zeroes i = replicate (fromIntegral i) f0
        in Matrix $ map (\(fromIntegral -> ki) ->
                           zeroes ki <> (reverse $ unPoly bchg) <> zeroes (bchN - l - ki))
                        [0..bchK-1]

-- | Input is BCH parameters and input word.
decodePGZ :: forall p. (PrimePoly p 2) => BCHCode p -> BVector -> BVector
decodePGZ BCHCode{..} c =
    trace (show slist :: Text) $
    trace (show ν :: Text) $
    trace (show mmatrix :: Text) $
    trace (show locs :: Text) $
    trace (show xlist :: Text) $
    trace (show ylist :: Text) $
    undefined
  where
    BCHParams{..} = bchParams
    t = (bchD - 1) `div` 2

    computeΛ m =
        gaussSolveSystem m $
        map fneg $ take (fromInteger ν) $ drop (fromInteger ν) slist

    computeM :: Integer -> Matrix (FinPoly p (Z 2))
    computeM (fromInteger -> μ) =
        Matrix $ map (\i -> take μ (drop i slist)) [0..μ-1]

    computeErrors i
        | i == 0 = error "computeErrors"
        | otherwise =
            let m = computeM i
            in if determinant m /= f0
               then i
               else computeErrors (i-1)

    ν = computeErrors $ t

    -- M
    mmatrix = computeM ν

    -- Λ_i
    locs :: [FinPoly p (Z 2)]
    locs = computeΛ mmatrix

    -- X_i
    xlist :: [FinPoly p (Z 2)]
    xlist = map finv locs

    ylist :: [FinPoly p (Z 2)]
    ylist =
        let xmatrix = Matrix $ map (\i -> map (<^> i) xlist) [0..ν-1]
        in gaussSolveSystem xmatrix (take (fromInteger ν) slist)

    -- input codeword is interpreted as low endian.
    -- c0 + c1x + c2x^2 + ...
    -- TODO use applyPoly
    slistFoo :: FinPoly p (Z 2) -> FinPoly p (Z 2)
    slistFoo αj =
        foldr (<+>) f0 $
        concat $
        map (\(b,i) -> if b then [αj <^> (i::Int)] else []) (c `zip` [0..])

    slist :: [FinPoly p (Z 2)]
    slist = map (slistFoo . (α <^>)) [fst bchPows..snd bchPows]

    α = getGen @(FinPoly p (Z 2))

testBCH :: IO ()
testBCH = do
    let bch = buildBCH @19 @2 7
    print bch
    let bchc = paramsToCode bch 15
    print bchc
    print $ checkGH (zToBool $ unMatrix $ bchG bchc) (zToBool $ unMatrix $ bchH bchc)
    let g = map (fromStrVec . map (head . (show :: Integer -> String) . unZ)) $
            unMatrix $ bchG bchc
    print $
        map showVec $
        take 20 $ codeG g
    --print $ decodePGZ bchc $ fromStrVec "110001100111011"
    print $ decodePGZ bchc $ fromStrVec "011101100101000"
    --print $ decodePGZ bchc $ fromStrVec "111001100011011"

--task76 :: IO ()
--task76 = do
--    let bch = buildBCH @67 @2 7
--    let bchc = paramsToCode bch 10
--    let g = map (fromStrVec . map (head . (show :: Integer -> String) . unZ)) $
--            unMatrix $ bchG bchc
--    print bchc
--    print $
--        map showVec $
--        take 20 $ codeG g
--    print $ decodePGZ bchc $ fromStrVec "0010100110"

{-

BCHCode {bchN = 15, bchK = 12,
bchParams = BCHParams {bchMs = [FinPoly [1,1,0,0],FinPoly [1,0]], bchPoly = FinPoly [1,0,1,1], bchPows = (1,4), bchD = 5, bchCyclotomic = [[3,6,12,9],[1,2,4,8]]},
bchG = Matrix {unMatrix =
[[1,1,0,1,0,0,0,0,0,0,0,0,0,0,0]
,[0,1,1,0,1,0,0,0,0,0,0,0,0,0,0]
,[0,0,1,1,0,1,0,0,0,0,0,0,0,0,0]
,[0,0,0,1,1,0,1,0,0,0,0,0,0,0,0]
,[0,0,0,0,1,1,0,1,0,0,0,0,0,0,0]
,[0,0,0,0,0,1,1,0,1,0,0,0,0,0,0]
,[0,0,0,0,0,0,1,1,0,1,0,0,0,0,0]
,[0,0,0,0,0,0,0,1,1,0,1,0,0,0,0]
,[0,0,0,0,0,0,0,0,1,1,0,1,0,0,0]
,[0,0,0,0,0,0,0,0,0,1,1,0,1,0,0]
,[0,0,0,0,0,0,0,0,0,0,1,1,0,1,0]
,[0,0,0,0,0,0,0,0,0,0,0,1,1,0,1]]}}
["000000000000000","000000000001101","000000000011010","000000000010111","000000000110100","000000000111001","000000000101110","000000000100011","000000001101000","000000001100101","000000001110010","000000001111111","000000001011100","000000001010001","000000001000110","000000001001011","000000011010000","000000011011101","000000011001010","000000011000111"]

-}
