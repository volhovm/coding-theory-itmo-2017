{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeInType                 #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE ViewPatterns               #-}

-- | Finite fields and stuff.

module Fields
    ( Ring(..)
    , (<->)
    , (<^>)
    , fastExp
    , times
    , Field(..)
    , Euclidian(..)
    , eDiv
    , eMod

    , gcdEucl

    , Z (..)
    , toZ
    , PrimeNat
    , Poly(..)
    , prettyPoly
    , deg
    , FinPoly (..)
    , mkFinPoly
    , isPrimePoly
    , PrimePoly
    , representBack
    , remakeFinPoly

    , gaussSolve
    ) where

import qualified Prelude
import           Universum    hiding ((<*>))
import           Unsafe       (unsafeHead, unsafeLast)

import           Control.Lens (ix, (%=), (.=))
import           Data.List    (nub, (!!))

----------------------------------------------------------------------------
-- Rings
----------------------------------------------------------------------------

class Eq a => Ring a where
    f0 :: a
    (<+>) :: a -> a -> a
    fneg :: a -> a
    f1 :: a
    (<*>) :: a -> a -> a

(<->) :: Ring a => a -> a -> a
(<->) a b = a <+> (fneg b)

times :: (Integral n, Ring a) => n -> a -> a
times (fromIntegral -> n) a = foldl' (<+>) f0 $ replicate n a

(<^>) :: (Integral n, Ring a) => a -> n -> a
(<^>) a (fromIntegral -> n) = foldl' (<*>) f1 $ replicate n a

-- | Fast powering algorithm for calculating a^p (mod p).
fastExp :: forall a n . (Ring a, Integral n) => a -> n -> a
fastExp g n = power g n
  where
    power :: a -> n -> a
    power _ 0 = f1
    power a 1 = a
    power a b = do
        let (bdiv,bmod) = b `divMod` 2
        let bnext = a `power` bdiv
        if | bmod == 0 -> bnext <*> bnext
           | otherwise -> bnext <*> bnext <*> a

instance Ring Integer where
    f0 = 0
    f1 = 1
    (<+>) = (+)
    fneg = negate
    (<*>) = (*)

class Ring a => Field a where
    finv :: a -> a
    -- ^ Multiplicative inverse
    getGen :: a
    -- ^ Generator
    getFieldSize :: Proxy a -> Integer
    -- ^ Field size

    default getFieldSize :: Proxy a -> Integer
    getFieldSize _ =
        let (g :: a) = getGen
            genPowers = iterate (\(i,x) -> (i+1,g <*> x)) (1,g)
        -- f0 + powers
        in 1 + fst (unsafeHead $ dropWhile ((/= f1) . snd) genPowers)

----------------------------------------------------------------------------
-- Integer ring/field
----------------------------------------------------------------------------

-- Z/nZ
newtype Z (a :: Nat) = Z { unZ :: Integer } deriving (Num, Eq, Ord, Enum, Real, Integral)

instance Show (Z a) where
    show (Z i) = show i

toZ :: forall n . (KnownNat n) => Integer -> Z n
toZ i = Z $ i `mod` (natVal (Proxy :: Proxy n))

class KnownNat n => PrimeNat (n :: Nat)

-- Too lazy to define it in any other way
#define GenZ(N) \
  instance PrimeNat N;\

GenZ(2)
GenZ(3)
GenZ(4)
GenZ(5)
GenZ(6)
GenZ(7)
GenZ(8)
GenZ(9)
GenZ(11)
GenZ(13)
GenZ(17)
GenZ(9539)

instance (KnownNat n) => Ring (Z n) where
    f0 = Z 0
    (Z a) <+> (Z b) = toZ $ a + b
    f1 = Z 1
    fneg (Z 0) = Z 0
    fneg (Z i) = toZ $ natVal (Proxy :: Proxy n) - i
    (Z a) <*> (Z b) = toZ $ a * b

-- | Naive search for any group generator.
findGenerator :: forall a. (Show a, Field a) => [a] -> a
findGenerator elems =
    fromMaybe (error "Couldn't find generator!") $
    find (\g -> let s = genOrderSet [] g g in length s == n - 1) $ filter (/= f0) elems
  where
    n = length elems
    genOrderSet acc g0 g | g == f1 = nub $ f1 : acc
                         | g `elem` acc = acc
                         | otherwise = genOrderSet (g:acc) g0 (g <*> g0)

instance (PrimeNat n) => Field (Z n) where
    finv (Z a) = toZ $ a `fastExp` (natVal (Proxy :: Proxy n) - 2)
    getGen = findGenerator $ map toZ [0..(natVal (Proxy :: Proxy n) - 1)]
    getFieldSize _ = natVal (Proxy :: Proxy n)

----------------------------------------------------------------------------
-- Polynomials
----------------------------------------------------------------------------

-- | Empty polynomial is equivalent to [0]. Big endian (head is higher
-- degree coefficient).
newtype Poly a = Poly [a] deriving (Functor)

instance Show a => Show (Poly a) where
    show (Poly l) = "Poly " ++ show l

-- Removes zeroes from the beginning
stripZ :: (Ring a) => Poly a -> Poly a
stripZ (Poly []) = Poly [f0]
stripZ r@(Poly [_]) = r
stripZ (Poly xs) =
    let l' = take (length xs - 1) xs
    in Poly $ dropWhile (== f0) l' ++ [unsafeLast xs]

prettyPoly :: forall a . (Show a, Ring a) => Poly a -> String
prettyPoly (stripZ -> (Poly p)) =
    intercalate " + " $
    map mapFoo $
    filter ((/= f0) . fst) $
    reverse $ reverse p `zip` [0..]
  where
    mapFoo :: (a,Integer) -> String
    mapFoo (n,0) = show n
    mapFoo (f,1) | f == f1 = "x"
    mapFoo (f,i) | f == f1 = "x^" ++ show i
    mapFoo (n,1) = show n ++ "x"
    mapFoo (n,i) = show n ++ "x^" ++ show i

instance (Ring a) => Eq (Poly a) where
    (==) (stripZ -> (Poly p1)) (stripZ -> (Poly p2)) = p1 == p2

deg ::  (Ring a, Integral n) => Poly a -> n
deg (stripZ -> (Poly p)) = fromIntegral $ length p - 1


-- Zips two lists adding zeroes to end of the shortest one
zip0 :: (Ring a) => [a] -> [a] -> [(a,a)]
zip0 p1 p2 = uncurry zip sameSize
  where
    shortest | length p1 < length p2 = (p1,p2)
             | otherwise = (p2,p1)
    diff = length (snd shortest) - length (fst shortest)
    sameSize = shortest & _1 %~ ((replicate diff f0) ++)

instance (Ring a) => Ring (Poly a) where
    f0 = Poly [f0]
    f1 = Poly [f1]
    fneg = fmap fneg
    (Poly p1) <+> (Poly p2) =
        stripZ $ Poly $ map (uncurry (<+>)) $ zip0 p1 p2
    lhs@(Poly p1) <*> rhs@(Poly p2) =
        let acc0 = replicate ((deg lhs + deg rhs)+1) f0
            foldFooSub acc ((e1,d1), (e2,d2)) =
                acc & ix (d1 + d2) %~ (<+> (e1 <*> e2))
            foldFoo acc ((e1,d1),el2) =
                foldl' foldFooSub acc $ map ((e1,d1),) $ withIndex el2
            withIndex a = reverse $ reverse a `zip` [0..]
        in stripZ . Poly $ reverse $ foldl' foldFoo acc0 $ map (,p2) $ withIndex p1

----------------------------------------------------------------------------
-- Euclidian
----------------------------------------------------------------------------

class Ring a => Euclidian a where
    (</>) :: a -> a -> (a,a)
    -- ^ Division with (quotient,remainder)

eDiv :: Euclidian a => a -> a -> a
eDiv a b = fst $ a </> b

eMod :: Euclidian a => a -> a -> a
eMod a b = snd $ a </> b

instance Euclidian Integer where
    (</>) a b = (a `div` b, a `mod` b)

instance KnownNat n => Euclidian (Z n) where
    (</>) (Z a) (Z b) =
        let wrap = (Z . (`mod` natVal (Proxy :: Proxy n)))
        in bimap wrap wrap (a `div` b, a `mod` b)

assert :: Bool -> Text -> a -> a
assert b str action = bool (error str) action b

-- | a / b = (quotient,remainder)
euclPoly :: (Field a) => Poly a -> Poly a -> (Poly a, Poly a)
euclPoly (stripZ -> a) (stripZ -> b@(Poly bPoly)) =
    let res@(q,r) = euclPolyGo f0 a
    in assert ((b <*> q) <+> r == a) "EuclPoly assert failed" res
  where
    euclPolyGo (stripZ -> q) (stripZ -> r)
        | (deg r :: Integer) < deg b || r == f0 = (q,r)
    euclPolyGo (stripZ -> q) (stripZ -> r@(Poly rPoly)) =
        let rDeg = deg r
            bDeg = deg b
            re = rPoly !! 0
            bd = bPoly !! 0
            x = Poly $ (re <*> (finv bd)) : replicate (rDeg - bDeg) f0
            q' = q <+> x
            r' = r <-> (x <*> b)
        in euclPolyGo q' r'

instance (Field a) => Euclidian (Poly a) where
    (</>) = euclPoly

gcdEucl :: (Euclidian a) => a -> a -> a
gcdEucl a b =
    let res = gcdEuclGo a b
    in assert (snd (a </> res) == f0) "gcd doesn't divide a" $
       assert (snd (b </> res) == f0) "gcd doesn't divide a" $
       res
  where
    gcdEuclGo r0 r1 =
        let (_,r) = r0 </> r1
        in if r == f0 then r1 else gcdEuclGo r1 r


----------------------------------------------------------------------------
-- Polynomials quotieng rings/fields
----------------------------------------------------------------------------

-- | Given a base and number, returns its power representation. Big
-- endian.
represent :: Integer -> Integer -> [Integer]
represent b i = reverse $ go i
  where go 0 = []
        go x = (x `mod` b) : (go $ x `div` b)

representBack :: Integer -> [Integer] -> Integer
representBack b poly = go 1 $ reverse poly
  where
    go :: Integer -> [Integer] -> Integer
    go _ []     = 0
    go i (x:xs) = (i * x) + go (i * b) xs

reflectCoeffPoly :: forall p n. (KnownNat n, KnownNat p) => Poly Integer
reflectCoeffPoly = Poly $ represent (natVal $ Proxy @n) (natVal $ Proxy @p)

getCoeffPoly :: forall p n. (KnownNat p, KnownNat n) => Poly (Z n)
getCoeffPoly = map toZ (reflectCoeffPoly @p @n)

-- Empty polynomial is equivalent for [0]. Head -- higher degree.
newtype FinPoly p a = FinPoly (Poly a) deriving Eq

instance (Show a) => Show (FinPoly p a) where
    show (FinPoly x) = "Fin" <> show x

allFinPolys :: forall p n. (KnownNat p, KnownNat n) => [FinPoly p (Z n)]
allFinPolys = map (FinPoly . stripZ . Poly . (map toZ)) $ binGen s
  where
    b :: Integer
    b = fromIntegral $ natVal (Proxy @n)
    s :: Integer
    s = deg (reflectCoeffPoly @p @n)
    binGen :: Integer -> [[Integer]]
    binGen 0 = [[]]
    binGen n =
        let x = binGen (n-1)
        in mconcat $ map (\i -> map (i :) x) [0..b-1]

isPrimePoly :: forall n . (KnownNat n, Euclidian (Poly (Z n))) => Poly (Z n) -> Bool
isPrimePoly p@(Poly pP) =
    let i = representBack (natVal $ Proxy @n) (map unZ pP)
        lesspolys :: [Poly (Z n)]
        lesspolys = map (Poly . map toZ . represent (natVal $ Proxy @n)) [2..(i-1)]
    in all (\pl -> p `eMod` pl /= f0) lesspolys

mkFinPoly :: forall p n . (KnownNat p, PrimeNat n) => Poly (Z n) -> FinPoly p (Z n)
mkFinPoly x = FinPoly $ (stripZ x) `eMod` getCoeffPoly @p

remakeFinPoly :: forall p n . (KnownNat p, PrimeNat n) => FinPoly p (Z n) -> FinPoly p (Z n)
remakeFinPoly (FinPoly x) = mkFinPoly x

instance (PrimeNat n, KnownNat p, Ring (Poly (Z n))) =>
         Ring (FinPoly p (Z n)) where
    f0 = mkFinPoly f0
    (<+>) (FinPoly p1) (FinPoly p2) = mkFinPoly (p1 <+> p2)
    fneg (FinPoly p1) = mkFinPoly $ (getCoeffPoly @p) <-> p1
    f1 = mkFinPoly f1
    (<*>) (FinPoly p1) (FinPoly p2) = mkFinPoly (p1 <*> p2)

instance (PrimeNat n, KnownNat p) => Euclidian (FinPoly p (Z n)) where
    (</>) (FinPoly p1) (FinPoly p2) = let (q,r) = p1 </> p2 in (mkFinPoly q, mkFinPoly r)

class PrimePoly (p :: Nat) (n :: Nat) where

-- 19 = x^4 + x + 1 is prime poly over F_2
instance PrimePoly 19 2
-- 67 = x^6 + x + 1 is prime poly over F_2
instance PrimePoly 67 2
-- 75 = x^6 + x^3 + x + 1 is NOT prime

instance (Ring (FinPoly p (Z n)), PrimePoly p n, PrimeNat n, KnownNat p)
         => Field (FinPoly p (Z n)) where
    finv (FinPoly f) =
        mkFinPoly $ f <^> (getFieldSize (Proxy @(FinPoly p (Z n))) - 2)
    getGen = findGenerator allFinPolys
    getFieldSize _ = do
        let b :: Integer
            b = fromIntegral $ natVal (Proxy @n)
        let s :: Integer
            s = deg (reflectCoeffPoly @p @n)
        (b ^ s)

_testFinPolys :: IO ()
_testFinPolys = do
    let pPoly = [1,0,0,1,1]
    let pEnc = representBack 2 pPoly
    let (x :: FinPoly 19 (Z 2)) = mkFinPoly (Poly [1,0])
    let z = x <^> (12 :: Int)
    let y = finv z
    print pEnc
    print $ z
    print $ y
    print $ z <*> y

----------------------------------------------------------------------------
-- Gauss
----------------------------------------------------------------------------

-- | Row dominated matrix
data Matrix a = Matrix [[a]] deriving Show

-- | You pass linear system [A|b], where A is n×n and get list of
-- solutions.
gaussSolve :: forall a. (Field a) => Matrix a -> Matrix a
gaussSolve (Matrix m0)
    | n > m = error "gaussSolve: n > m"
    | otherwise = Matrix $ execState (diagonal1 >> diagonal2) m1
  where
    ix2 :: Int -> Int -> State [[a]] a
    ix2 i j = do (x :: [a]) <- use (ix i)
                 pure $ x !! j

    n = length m0
    m = length $ unsafeHead m0

    diagonal1 :: State [[a]] ()
    diagonal1 = forM_ [0..(n-1)] $ \(i::Int) -> do
        -- Dividing by diagonal coefficient
        k0 <- ix2 i i
        -- If we're encountered empty row, we swap it with the first
        -- non-zero row. If there is no, we fail.
        k <- if k0 /= f0 then pure k0 else do
                 otherCoeffs <- forM [i+1..(n-1)] $ \j -> (j,) <$> ix2 j i
                 let alt = find (\(_,v) -> v /= f0) otherCoeffs
                 case alt of
                     Nothing -> error "Empty line, can't swap"
                     Just (j,k') -> do
                         rowJ <- use (ix j)
                         rowI <- use (ix i)
                         ix i .= rowI
                         ix j .= rowJ
                         pure k'

        let km1 = finv k
        forM_ [i..(m-1)] $ \j -> (ix i . ix j) %= (<*> km1)

        -- For all lower levels, adding
        forM_ [i+1..(n-1)] $ \j -> do
            s <- ix2 j i
            forM_ [i..m] $ \y -> do
                x <- ix2 i y
                ix j . ix y %= (\e -> e <-> (s <*> x))

    diagonal2 :: State [[a]] ()
    diagonal2 = forM_ (reverse [0..(n-1)]) $ \(i::Int) -> do
        -- For all upper levels, adding
        forM_ [0..i-1] $ \j -> do
            s <- ix2 j i
            forM_ [i..(m-1)] $ \y -> do
                x <- ix2 i y
                ix j . ix y %= (\e -> e <-> (s <*> x))

    initialSort :: [[a]] -> [[a]]
    initialSort = sortBy (comparing $ length . takeWhile (== f0))

    m1 :: [[a]]
    m1 = initialSort m0

_testGauss :: IO ()
_testGauss = print $ gaussSolve m
  where
    (m :: Matrix (Z 9539)) = Matrix $ map (map toZ) [[2,6,1,3030,1],[11,2,0,6892,2],[4,1,3,18312,3]]

_testGenerators :: IO ()
_testGenerators = do
    print $ getGen @(Z 17)
    let (g :: Poly (Z 2)) = Poly [1,1,1]
    print g
    print (finv (Z 1 :: Z 2))
    let h = Poly [1,1]
    print h
    print $ g `euclPoly` h
    print $ take 20 $ iterate (<*> g) g
    print (allFinPolys :: [FinPoly 19 (Z 2)])
    print $ getGen @(FinPoly 19 (Z 2))
    print $ getFieldSize (Proxy @(FinPoly 19 (Z 2)))
    print $ allFinPolys @75 @2

_testPrimality :: IO ()
_testPrimality = do
    print $ isPrimePoly $ (Poly [1,0,0,1,1] :: Poly (Z 2))
    print $ isPrimePoly $ (Poly [1,1,1] :: Poly (Z 2))
    print $ isPrimePoly $ (Poly [1,0,1,1] :: Poly (Z 2))
    print $ isPrimePoly $ (Poly [1,0,1,1] :: Poly (Z 2))
    print $ isPrimePoly $ (Poly [1,0,0,0,1,1,1,0,1] :: Poly (Z 2))
    print $ (Poly (map toZ $ represent 2 67) :: Poly (Z 2))
    print $ isPrimePoly $ (Poly (map toZ $ represent 2 75) :: Poly (Z 2))
    print $ isPrimePoly $ (Poly (map toZ $ represent 2 57) :: Poly (Z 2))
    print $ isPrimePoly $ (Poly (map toZ $ represent 2 67) :: Poly (Z 2))
    print $ isPrimePoly $ (Poly (map toZ $ represent 2 51) :: Poly (Z 2))
