{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DefaultSignatures   #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE TypeInType          #-}


module Fields where


import qualified Prelude
import Universum hiding (head, last, (<*>))

import Control.Lens (ix, (%=), (.=))
import Data.List (head, last, (!!))
import qualified Data.List as L

----------------------------------------------------------------------------
-- Typeclasses and misc
----------------------------------------------------------------------------

-- Disclaimer: this hierarchy is not optimal. For instance,
-- multiplicative groups can't be exressed at all :shrug:.

-- Addition group.
class Eq a => AGroup a where
    f0 :: a

    infixl 5 <+>
    (<+>) :: a -> a -> a

    fneg :: a -> a

    -- In case it can be implemented more efficiently.
    infixl 6 `times`
    times :: Integer -> a -> a
    default times :: Integer -> a -> a
    times = fastTimes

infixl 5 <->
(<->) :: AGroup a => a -> a -> a
(<->) a b = a <+> (fneg b)

-- | Slow linear "times" implementation.
linearTimes :: forall a. (AGroup a) => Integer -> a -> a
linearTimes n a = foldl' (<+>) f0 $ replicate (fromIntegral n) a

-- | Double-and-add.
fastTimes :: forall a. (AGroup a) => Integer -> a -> a
fastTimes n0 a = tms n0
  where
    tms :: Integer -> a
    tms 0 = f0
    tms 1 = a
    tms n = do
        let (ndiv,nmod) = n `divMod` 2
        let nnext = tms ndiv
        if | nmod == 0 -> nnext <+> nnext
           | otherwise -> nnext <+> nnext <+> a

class (Eq a, AGroup a) => Ring a where
    f1 :: a

    infixl 6 <*>
    (<*>) :: a -> a -> a

    infixl 7 <^>
    (<^>) :: a -> Integer -> a
    default (<^>) :: a -> Integer -> a
    (<^>) = fastExp

-- | Linear exponentiation by multiplication.
linearExp :: Ring a => a -> Integer -> a
linearExp a n = foldl' (<*>) f1 $ replicate (fromIntegral n) a

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

-- | Searchs for the generator given op and list of elements to
-- produce (also to choose from). For multiplicative group it should
-- be used with (<*>) and (allElems \\ f0), since 0 is not produced.
findGenerator :: forall a. (Eq a) => (a -> a -> a) -> [a] -> a
findGenerator op elems =
    fromMaybe (error $ "findGenerator: didn't manage to") $
    find (\g -> let s = genOrderSet [] g g in length s == n) elems
  where
    n = length elems
    genOrderSet acc g0 g | g `elem` acc = acc
                         | otherwise = genOrderSet (g:acc) g0 (g `op` g0)

-- Field.
class Ring a => Field a where
    finv :: a -> a
    -- ^ Multiplicative inverse.

-- Finite field.
class Field a => FField a where
    getGen :: a
    -- ^ Generator.
    allElems :: [a]
    -- ^ List all elements.
    getFieldSize :: Proxy a -> Integer
    -- ^ Field size.

    default allElems :: [a]
    allElems =
        let (g :: a) = getGen
            genPowers = iterate (g <*>) g
        -- f0 + powers
        in f0:(dropWhile (/= f1) genPowers)

    default getFieldSize :: Proxy a -> Integer
    getFieldSize _ = fromIntegral $ length (allElems @a)

    default getGen :: a
    getGen = findGenerator (<*>) (L.delete f0 allElems)

----------------------------------------------------------------------------
-- Integer
----------------------------------------------------------------------------

instance AGroup Integer where
    f0 = 0
    (<+>) = (+)
    fneg = negate

instance Ring Integer where
    f1 = 1
    (<*>) = (*)

----------------------------------------------------------------------------
-- Double/rational
----------------------------------------------------------------------------

instance AGroup Double where
    f0 = 0
    (<+>) = (+)
    fneg = negate

instance Ring Double where
    f1 = 1
    (<*>) = (*)

instance Field Double where
    finv x = 1/x


instance AGroup Rational where
    f0 = 0
    (<+>) = (+)
    fneg = negate

instance Ring Rational where
    f1 = 1
    (<*>) = (*)

instance Field Rational where
    finv x = 1/x

----------------------------------------------------------------------------
-- Finite integer ring/field
----------------------------------------------------------------------------

natValI :: forall n. KnownNat n => Integer
natValI = toInteger $ natVal (Proxy @n)

-- Z/nZ
newtype Z (a :: Nat) = Z { unZ :: Integer } deriving (Num, Eq, Ord, Enum, Real, Integral, Generic, Hashable)

instance Show (Z a) where
    show (Z i) = show i

toZ :: forall n . (KnownNat n) => Integer -> Z n
toZ i = Z $ i `mod` (natValI @n)

class KnownNat n => PrimeNat (n :: Nat)

-- Sadly, I do not know a better way to solve this problem. It'd be
-- nice if GHC ran primality test every time he was checking the
-- instance. I think I could at least use TH to pre-generate first k
-- primes. Also if this is tedious to use, one can just define
-- "instance KnownNat n => PrimeNat n" and forget about this check.
#define DefPrime(N) instance PrimeNat N;\

DefPrime(2)
DefPrime(3)
DefPrime(4)
DefPrime(5)
DefPrime(6)
DefPrime(7)
DefPrime(8)
DefPrime(9)
DefPrime(11)
DefPrime(13)
DefPrime(17)
DefPrime(19)
DefPrime(23)
DefPrime(29)
DefPrime(41)
DefPrime(47)
DefPrime(53)
DefPrime(59)
DefPrime(83)
DefPrime(613)
DefPrime(631)
DefPrime(691)
DefPrime(883)
DefPrime(1009)
DefPrime(1051)
DefPrime(1201)
DefPrime(1321)
DefPrime(1723)
DefPrime(1999)
DefPrime(2671)
DefPrime(3221)
DefPrime(9539)
DefPrime(17389)

instance (KnownNat n) => AGroup (Z n) where
    f0 = Z 0
    (Z a) <+> (Z b) = toZ $ a + b
    fneg (Z 0) = Z 0
    fneg (Z i) = toZ $ natValI @n - i

instance (KnownNat n) => Ring (Z n) where
    f1 = Z 1
    (Z a) <*> (Z b) = toZ $ a * b


instance (PrimeNat n) => Field (Z n) where
    finv (Z a) = toZ $ a `fastExp` (natValI @n - 2)
instance (PrimeNat n) => FField (Z n) where
    getFieldSize _ = natValI @n
    allElems = map toZ $ [0..(natValI @n - 1)]

----------------------------------------------------------------------------
-- Polynomials
----------------------------------------------------------------------------

-- | Empty polynomial is equivalent to [0]. Big endian (head is higher
-- degree coefficient).
newtype Poly a = Poly { unPoly :: [a] } deriving (Functor,Ord,Generic)

deriving instance Hashable a => Hashable (Poly a)

instance Show a => Show (Poly a) where
    show (Poly l) = "Poly " ++ show l

-- Removes zeroes from the beginning
stripZ :: (AGroup a) => Poly a -> Poly a
stripZ (Poly []) = Poly [f0]
stripZ r@(Poly [_]) = r
stripZ (Poly xs) =
    let l' = take (length xs - 1) xs
    in Poly $ dropWhile (== f0) l' ++ [last xs]

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

instance (AGroup a) => Eq (Poly a) where
    (==) (stripZ -> (Poly p1)) (stripZ -> (Poly p2)) = p1 == p2

deg ::  (Ring a, Integral n) => Poly a -> n
deg (stripZ -> (Poly p)) = fromIntegral $ length p - 1

applyPoly :: (FField a) => Poly a -> a -> a
applyPoly (stripZ -> (Poly p)) v =
    foldr (<+>) f0 $
        map (\(b,i) -> b <*> (v <^> (i::Integer)))
            (reverse p `zip` [0..])

-- Zips two lists adding zeroes to end of the shortest one
zip0 :: (AGroup a) => [a] -> [a] -> [(a,a)]
zip0 p1 p2 = uncurry zip sameSize
  where
    shortest | length p1 < length p2 = (p1,p2)
             | otherwise = (p2,p1)
    diff = length (snd shortest) - length (fst shortest)
    sameSize = shortest & _1 %~ ((replicate diff f0) ++)

instance (AGroup a) => AGroup (Poly a) where
    f0 = Poly [f0]
    fneg = fmap fneg
    (Poly p1) <+> (Poly p2) =
        stripZ $ Poly $ map (uncurry (<+>)) $ zip0 p1 p2

instance (Ring a) => Ring (Poly a) where
    f1 = Poly [f1]
    lhs@(Poly p1) <*> rhs@(Poly p2) =
        let acc0 :: [a]
            acc0 = replicate ((deg lhs + deg rhs)+1) f0
            withIndex :: [a] -> [(a,Int)]
            withIndex a = reverse $ reverse a `zip` [0..]

            foldFooSub :: [a] -> ((a,Int),(a,Int)) -> [a]
            foldFooSub acc ((e1,d1), (e2,d2)) =
                acc & ix (d1 + d2) %~ (<+> (e1 <*> e2))
            foldFoo :: [a] -> ((a,Int),[a]) -> [a]
            foldFoo acc ((e1,d1),el2) =
                foldl' foldFooSub acc $ map ((e1,d1),) $ withIndex el2
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
        let wrap = (Z . (`mod` natValI @n))
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

-- | For a,b returns (gcd,u,v) such that au + bv = gcd.
extendedEucl' :: (Euclidian n) => n -> n -> (n, n, n)
extendedEucl' a b
    | a == f0 = (b, f0, f1)
    | otherwise =
        let (g,s,t) = extendedEucl (b `eMod` a) a
        in (g, t <-> (b `eDiv` a) <*> s, s)

extendedEucl :: (Euclidian n) => n -> n -> (n, n, n)
extendedEucl a b =
    let res@(g,u,v) = extendedEucl' a b in
      if | u <*> a <+> v <*> b /= g -> error "extendedEucl is broken 1"
         | a `eMod` g /= f0 -> error "extendedEucl is broken 2"
         | b `eMod` g /= f0 -> error "extendedEucl is broken 3"
         | otherwise -> res

findRoots :: forall a. (FField a) => Poly a -> [a]
findRoots x = go elems0 x
  where
    go [] _ = []
    go (e:es) p = let y = Poly [f1,f0] <-> Poly [e]
                      (q,r) = p </> y
                  in if r == f0 then e : go (e:es) q else go es p
    elems0 = allElems @a

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
reflectCoeffPoly = Poly $ represent (natValI @n) (natValI @p)

getCoeffPoly :: forall p n. (KnownNat p, KnownNat n) => Poly (Z n)
getCoeffPoly = map toZ (reflectCoeffPoly @p @n)

-- Empty polynomial is equivalent for [0]. Head -- higher degree.
newtype FinPoly (p :: Nat) a = FinPoly { unFinPoly :: Poly a } deriving (Eq,Ord,Generic)

deriving instance Hashable (Poly a) => Hashable (FinPoly p a)

type FinPolyZ p n = FinPoly p (Z n)

instance (Show a) => Show (FinPoly p a) where
    show (FinPoly x) = "Fin" <> show x

allFinPolys :: forall p n. (KnownNat p, KnownNat n) => [FinPoly p (Z n)]
allFinPolys = map (FinPoly . stripZ . Poly . (map toZ)) $ binGen s
  where
    b :: Integer
    b = fromIntegral $ natValI @n
    s :: Integer
    s = deg (reflectCoeffPoly @p @n)
    binGen :: Integer -> [[Integer]]
    binGen 0 = [[]]
    binGen n =
        let x = binGen (n-1)
        in mconcat $ map (\i -> map (i :) x) [0..b-1]

isPrimePoly :: forall n . (KnownNat n, Euclidian (Poly (Z n))) => Poly (Z n) -> Bool
isPrimePoly p@(Poly pP) =
    let i = representBack (natValI @n) (map unZ pP)
        lesspolys :: [Poly (Z n)]
        lesspolys = map (Poly . map toZ . represent (natValI @n)) [2..(i-1)]
    in all (\pl -> p `eMod` pl /= f0) lesspolys

mkFinPoly :: forall p n . (KnownNat p, PrimeNat n) => Poly (Z n) -> FinPoly p (Z n)
mkFinPoly x = FinPoly $ (stripZ x) `eMod` getCoeffPoly @p

type FinPolyNats p n = (KnownNat p, PrimeNat n)

instance (FinPolyNats p n) => AGroup (FinPoly p (Z n)) where
    f0 = mkFinPoly f0
    (<+>) (FinPoly p1) (FinPoly p2) = mkFinPoly (p1 <+> p2)
    fneg (FinPoly p1) = mkFinPoly $ (getCoeffPoly @p) <-> p1

instance (FinPolyNats p n) => Ring (FinPoly p (Z n)) where
    f1 = mkFinPoly f1
    (<*>) (FinPoly p1) (FinPoly p2) = mkFinPoly (p1 <*> p2)

instance FinPolyNats p n => Euclidian (FinPoly p (Z n)) where
    (</>) (FinPoly p1) (FinPoly p2) = let (q,r) = p1 </> p2 in (mkFinPoly q, mkFinPoly r)

class FinPolyNats p n => PrimePoly (p :: Nat) (n :: Nat) where

-- 19 = x^4 + x + 1 is prime poly over F_2
instance PrimePoly 19 2
-- 67 = x^6 + x + 1 is prime poly over F_2
instance PrimePoly 67 2
-- 75 = x^6 + x^3 + x + 1 is NOT prime
-- 11 = x^3 + x + 1 is prime poly over F_2
instance PrimePoly 11 2
-- ℂ: x^2 + 1 for p = 3 (mod 4)
instance PrimePoly 362 19
instance PrimePoly 2210 47
instance PrimePoly 477482 691
instance PrimePoly 2968730 1723

invFinPolyFermat :: forall p n. (KnownNat p, PrimeNat n) => FinPoly p (Z n) -> FinPoly p (Z n)
invFinPolyFermat f =
    let b = fromIntegral (natValI @n) :: Integer
        s = deg (reflectCoeffPoly @p @n) :: Integer
        phi = (b ^ s) - 1 -- http://www.dtic.mil/dtic/tr/fulltext/u2/a218148.pdf
        res = f <^> (phi - 1) -- because f^φ = 1
    in if res <*> f /= f1 then error "invFinPolyFermat failed" else res

instance (PrimePoly p n) => Field (FinPoly p (Z n)) where
    finv = invFinPolyFermat

instance (PrimePoly p n) => FField (FinPoly p (Z n)) where
    allElems = allFinPolys
    getFieldSize _ =
        let b = fromIntegral (natValI @n) :: Integer
            s = deg (reflectCoeffPoly @p @n) :: Integer
        in (b ^ s)

irreducablePoly :: forall n. (PrimeNat n) => Integer -> Poly (Z n) -> Bool
irreducablePoly d (stripZ -> a) =
    let n = natValI @n
        l = representBack n $ 1 : replicate (fromIntegral d) 0
        ps = drop (fromIntegral n) $ (map (stripZ . Poly . map (toZ @n) . represent n) [0..(l-1)])
    in all (\x -> a `eMod` x /= f0) ps

_testFinPolys :: IO ()
_testFinPolys = do
    let pPoly = [1,0,0,1,1]
    let pEnc = representBack 2 pPoly
    let (x :: FinPoly 19 (Z 2)) = mkFinPoly (Poly [1,0])
    let z = x <^> 12
    let y = finv z
    print pEnc
    print $ z
    print $ y
    print $ z <*> y


-- | Row dominated matrix
data Matrix a = Matrix { unMatrix :: [[a]] } deriving Show

-- | Matrix (n,m) size.
msize :: Matrix a -> (Int,Int)
msize (Matrix l) = (length l, length (head l))

vmulm :: Ring a => [a] -> Matrix a -> [a]
vmulm v (Matrix m) = map (product' v) (transpose m)
  where
    product' a b = foldl' (<+>) f0 (zipWith (<*>) a b)

mmulm :: Ring a => Matrix a -> Matrix a -> Matrix a
mmulm (Matrix m1) (Matrix m2) = Matrix $ transpose $ map (`vmulm` Matrix m2) m1


-- | Matrix minor.
minor :: Matrix a -> Int -> Int -> Matrix a
minor (Matrix rows) i j = Matrix $ map (dropAround j) $ dropAround i rows
  where
    dropAround 0 l = drop 1 l
    dropAround k l | k == length l - 1 = take (length l - 1) l
    dropAround k l = take k l <> drop (k+1) l

-- | Matrix's determinant. Works only for square matrices.
determinant :: Ring a => Matrix a -> a
determinant (Matrix s) | length s /= length (head s) = error "determinant: matrix is not square"
determinant (Matrix [[x]]) = x
determinant m@(Matrix rows) =
    foldr1 (<+>) $
    map (\((e,k),i) -> k <*> e <*> determinant (minor m 0 i))
        ((head rows `zip` cycle [f1,fneg f1]) `zip` [0..])

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
    m = length $ head m0

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

-- | v * X = y, solves for v
gaussSolveSystem :: forall a. (Field a) => Matrix a -> [a] -> [a]
gaussSolveSystem m x =
    case () of
      () | length res /= length (head (unMatrix m)) -> error "gaussSolveSystem: dimensions"
         | not check -> error "gaussSolveSystem: failed"
         | otherwise -> res
  where
    check = and $ map (\(r,v) -> foldr1 (<+>) (map (\(a,b) -> a <*> b) $ zip r res) == v) $ unMatrix m `zip` x
    m' = Matrix $ map (\(r,v) -> r ++ [v]) $ unMatrix m `zip` x
    res = map last $ unMatrix $ gaussSolve m'
