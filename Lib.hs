{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TypeApplications  #-}
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


import           Nub                      (ordNub)
import           Universum                hiding (transpose)
import           Unsafe                   (unsafeHead, unsafeLast)

import           Control.Concurrent.Async
import           Control.Lens             (at, ix, (?=))
import qualified Data.HashSet             as HS
import           Data.List                (findIndex, (!!))
import           Data.Map.Strict          ((!))
import qualified Data.Map.Strict          as M
import           Graphics.EasyPlot
import           System.IO.Unsafe         (unsafePerformIO)
import           System.Random


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
type BMatrix = [BVector]

showVec :: BVector -> String
showVec = map $ bool '0' '1'

showM :: BMatrix -> String
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
    n = length (unsafeHead m1)

vMulM :: BVector -> BMatrix -> BVector
vMulM v m = map (scalar v) m

mMulM :: BMatrix -> BMatrix -> BMatrix
mMulM a b = transpose $ map (`vMulM` b) $ transpose a

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
    n = length $ unsafeHead vectors
    zero = replicate n False
    sumAll :: [BVector] -> BVector
    sumAll = foldr sumBVectors $ replicate (length $ unsafeHead vectors) False
    ps :: [[BVector]]
    ps = concatMap (flip combinations vectors) [1..(min d (fromIntegral $ length vectors))]


-- | Checks if any combination of given vectors can be linear dependent.
linearDependent :: [BVector] -> Bool
linearDependent vectors =
    linearDependentSubset (fromIntegral $ length vectors) vectors

distance :: [BVector] -> Integer
distance matrix =
    (+1) $ fromMaybe 0 $ find hasDistance $ reverse [1..maxRank]
  where
    hasDistance :: Integer -> Bool
    hasDistance i = not (linearDependentSubset i matrix)
    n = length (unsafeHead matrix)
    k = length matrix
    maxRank :: Integer
    maxRank = toInteger $ min n k

encodeG :: BMatrix -> BVector -> BVector
encodeG g x = x `vMulM` g

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

task27 :: Map BVector BVector
task27 = syndromDecodeBuild h23

task26 :: Map BVector BVector
task26 = syndromDecodeBuild h
  where
    h = drop 1 $ binaryVectors (3::Int)

-- | Returns complete list of code vectors by H.
codeH :: [BVector] -> [BVector]
codeH h = filter (\y -> y `vMulM` (transpose h) == replicate r False)
                 (binaryVectors n)
  where
    n = length h
    r = length (unsafeHead h)

-- | Get all code words from G.
codeG :: [BVector] -> [BVector]
codeG g = map (`vMulM` g) $ binaryVectors k
  where
    k = length (unsafeHead g)

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

-- | Checks if g and h are compatible.
checkGH :: BMatrix -> BMatrix -> Bool
checkGH g h = isNullM $ g `mMulM` transpose h

-- | Finds g given h.
findGfromH :: [BVector] -> [BVector]
findGfromH h =
    fromMaybe (error "can't happen2") $
    find (\g -> formsBasis g && checkGH g h) allPossibleG
  where
    formsBasis g = not $ linearDependent $ transpose g

    allPossibleG = combinations (fromIntegral n) $ binaryVectors k
    n = length h
    r = length $ unsafeHead h
    k = n - r

hamming74H = drop 1 $ binaryVectors (3 :: Int)
hamming74G = findGfromH hamming74H
hammingE84H = map (++ [True]) $ binaryVectors (3 :: Int)
hammingE84G = findGfromH hammingE84H

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
    map fromIntVector $ transpose
    [ [1, 0, 0, 0, 0, 0, 1, 1, 1, 1]
    , [0, 1, 0, 0, 0, 0, 1, 1, 1, 0]
    , [0, 0, 1, 0, 0, 0, 0, 1, 0, 1]
    , [0, 0, 0, 1, 0, 0, 0, 1, 1, 0]
    , [0, 0, 0, 0, 1, 0, 1, 1, 0, 0]
    , [0, 0, 0, 0, 0, 1, 1, 0, 1, 0]
    ]

h23Dimq :: BMatrix
h23Dimq =
    map fromIntVector $ transpose
    [ [1, 1, 0, 0, 1, 1, 1, 0, 0, 0]
    , [1, 1, 1, 1, 1, 0, 0, 1, 0, 0]
    , [1, 1, 0, 1, 0, 1, 0, 0, 1, 0]
    , [1, 0, 1, 0, 0, 0, 0, 0, 0, 1]
    ]

----------------------------------------------------------------------------
-- Part 3
----------------------------------------------------------------------------

findDRange :: Integer -> Integer -> (Integer,Integer)
findDRange n k = (lastB hammingCond [1..n], lastB gilbertVarshamovCond [1..n])
  where
    lastB cond = unsafeLast . takeWhile cond
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
    let g = g23Dimq
    let n :: Integer
        n = fromIntegral $ length g23
    let log10 x = log x / log 10
    let code = codeG g
    let diffV x y = weight $ x `sumBVectors` y
    rVecs <- map (code !!) <$> replicateM (fromInteger i) (randomRIO (0,length code - 1))
    let funcGen :: Encoder -> Decoder -> IO Double
        funcGen encoder decoder = do
            let foo :: BVector -> [Double] -> Double
                foo x c = fromIntegral $ decoder c `diffV` x
            rVecsEnc <- forM rVecs $ \r -> (r,) <$> mapM encoder r
            let nm = sum (map (uncurry foo) rVecsEnc)
            let dnm = fromIntegral $ i * n
            putText $ show nm <> " / " <> show dnm <> " = " <> (show $ nm / dnm)
            pure $ nm / dnm
    let fromdecibels :: Double -> Double
        fromdecibels x = 10 ** (x / 10)
    let dscDo decoder (fromdecibels -> en0) =
            let func1Raw e = funcGen (dscEncode e) (decoder (dsc e) code)
            in log10 <$> func1Raw (calcp en0)
    let awgnDo decoder (fromdecibels -> en0) = fmap log10 $ do
            let e = 5
            let n0 = e / en0
            funcGen (awgnEncode n0 e) (decoder (awgn n0 e) code)
    let func1 = dscDo decodeML
    let func1mAp = dscDo decodeMaxAp
    let func2 = awgnDo decodeML
    let func2mAp = awgnDo decodeMaxAp
    let funcrange = [-2..4]++[4.5,4.7..8]
    let f2d (t,f) = Data2D [Title t, Style Lines] [] f
    (datasets :: [(String,[(Double,Double)])]) <-
        mapConcurrently
        (\(t,f) -> do
              putStrLn $ "Evaluating " <> t
              points <- mapM (\x -> (x,) <$> f x) funcrange
              pure $ (t,points))
        [ ("DSC, ML", func1)
        , ("DSC, MAP", func1mAp)
        , ("AWGN, ML", func2)
        , ("AWGN, MAP", func2mAp) ]
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
    r = length $ unsafeHead h
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
