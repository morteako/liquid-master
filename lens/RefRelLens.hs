{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--no-adt"     @-}

{-# LANGUAGE RankNTypes #-}

import Language.Liquid.Haskell.ProofCombinators

{-@ reflect un @-}
{-@ lazy un @-}
un = un

type FLens s t a b = forall f. Functor f => (a -> f b) -> s -> f t


-- {-@ reflect constfmap @-}
{-@ constfmap :: f:(a -> b) -> c:Const m a -> cc:Const m c  @-}
constfmap :: (a -> b) -> Const m a -> Const m c
constfmap _ (Const a) = Const a

instance Functor (Const a) where
    fmap = constfmap

instance Functor (Identity) where
    fmap = idfmap

{-@ data Const a b = Const {unConst :: a} @-}
data Const a b = Const {unConst :: a}


-- {-@ reflect view @-}
view :: FLens s t a b -> s -> a
view lens s = unConst (lens Const s)

-- {-@ viewRef :: forall s <p :: s -> s -> Bool> . RefLens <p> s t a b -> s<p> -> a @-}
-- viewRef :: RefLens s t a b -> s -> a
-- viewRef (RefLens lens) = view lens 

{-@ assume setRefList :: 
    FLens [a] [a] a a -> a -> xs:[a] -> {ys:[a] | len xs == len ys} @-}
setRefList :: FLens [a] [a] a a -> a -> [a] -> [a]
setRefList lens = set lens

-- {-@ reflect set @-}
{-@ set :: lens:FLens s t a b -> v:b -> val:s -> res:t @-}
set :: FLens s t a b -> b -> s -> t
set lens b s = runIdentity (lens  (constIdentity b) s)


-- {-@ reflect over @-}
-- {-@ over :: lens:FLens s t a b -> v:b -> val:s -> res:t @-}
over :: FLens s t a b -> (a -> b) -> s -> t
over lens f s = runIdentity (lens (Identity . f) s)



-- {-@ type RefLens s t a b <l :: a -> b -> Bool>  = FLens s t a b  @-}

{-@ data RefLens s t a b  <sp :: s -> Bool, p :: s -> t -> Bool> = 
    RefLens (FLens (source:s)<sp> t<p source> a b) @-}
data RefLens s t a b = RefLens {getRefLens ::(FLens s t a b)}    



{-@ data Identity a = Identity {runIdentity :: a} @-}
data Identity a = Identity {runIdentity :: a}

-- {-@ reflect idfmap @-}
{-@ idfmap :: f:(a -> b) -> ia:Identity a -> ib:Identity b @-}
idfmap :: (a -> b) -> Identity a -> Identity b
idfmap f (Identity a) = Identity (f a)

-- {-@ reflect constIdentity @-}
{-@ constIdentity :: x:a -> v:b -> r:Identity a @-}
constIdentity :: a -> b -> Identity a
constIdentity a _ = Identity a

-- {-@ data D = A | B  @-}
data D = A | B deriving Show

-- type FLens s t a b = forall f. (forall a b . (a -> b) -> f a -> f b) -> (a -> f b) -> s -> f t
type FLens' s a = FLens s s a a


{-@ data DPair = DPair {x :: Nat, y :: D} @-}
data DPair = DPair {x :: Int, y :: D} deriving Show

-- {-@ reflect dpairFlipped @-}
{-@ dpairFlipped :: D -> Nat -> DPair @-}
dpairFlipped :: D -> Int -> DPair
dpairFlipped y x = DPair x y

-- {-@ reflect xLens @-}
{-@  xLens :: FLens DPair DPair Nat Nat @-} 
-- xLens :: FLens' DPair Int
xLens afb (DPair x y) = fmap (dpairFlipped y) (afb x)

dp = DPair 1 A

-- {-@ reflect n @-}
{-@ n :: Nat @-}
n = view xLens (DPair 1 A)
d = set xLens 2 (DPair 1 A)
d2 = over xLens (*2) (DPair 1 A)

{-@ data P = P {px :: DPair, py :: DPair} @-}
data P = P {px :: DPair, py :: DPair} deriving Show

-- {-@ reflect pyLens @-}
{-@  pyLens :: FLens' P DPair @-} 
pyLens :: FLens' P DPair
pyLens afb (P x y) = fmap (P x) (afb y)

{-@ assume compose :: FLens' P DPair -> FLens' DPair Nat -> FLens' P Nat @-}
compose :: FLens' P DPair -> FLens' DPair Int -> FLens' P Int 
compose f g x = f (g x)

{-@ assume comp :: forall s a x <p :: x -> Bool> . FLens' s a -> FLens' a x<p> -> FLens' s x<p> @-}
-- comp :: FLens' P DPair -> FLens' DPair Int -> FLens' P Int
comp :: FLens' s a -> FLens' a x -> FLens' s x 
comp f g = f . g

{-@  pyXLens :: FLens' P Nat @-} 
pyXLens :: FLens' P Int
pyXLens afb (P x (DPair x' y)) = fmap (P x . dpairFlipped y) (afb x')

{-@ noe :: FLens' P Nat @-}
noe :: FLens' P Int
noe = pyLens . xLens

s = view (compose pyLens xLens) (P dp dp)
s' = view noe (P dp dp)
-- s'' = view (pyLens . xLens) (P dp dp)
s2 = view (pyXLens) (P dp dp)


-- {-@ ix1 :: {i:Int | i == 0] -> FLens [a] [b] a b} @-}
-- ix1 :: Int -> FLens [a] [b] a b
-- ix1 i afb 

{-@ ix :: i:Nat -> RefLens <{\s -> len s > i},{\s t -> len s == len t}> [a] [a] a a @-}
ix :: Int -> RefLens [a] [a] a a
ix n = RefLens (\afb xs -> let (pre,x,post) = split n xs in fmap (\y -> pre ++ y:post) (afb x))


{-@ split :: i:Nat -> {xs:[a] | len xs > i} -> ([a],a,[a]) @-}
split :: Int -> [a] -> ([a],a,[a])
split n xs = (pre,p,post)
    where
    (pre,p:post) = splitAt n xs

-- ixTest = viewRef (ix 0) [1,2,3] 

{-@ ixTest2 :: {v:[Integer] | len v == 3} @-}
ixTest2 = set (ix 1) 0 [1,2,3] 

