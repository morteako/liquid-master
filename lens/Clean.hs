-- {-@ LIQUID "--ple"                  @-}
{-@ LIQUID "--reflection"           @-}
{-@ LIQUID "--no-adt"               @-}
{-@ LIQUID "--prune-unsorted"      @-}

{-# LANGUAGE RankNTypes #-}

-- import Language.Liquid.Haskell.ProofCombinators

{-@ reflect un @-}
{-@ lazy un @-}
un = un

type Lens s t a b = forall f. Functor f => (a -> f b) -> s -> f t

-- {-@ reflect constfmap @-}
{-@ constfmap :: f:(a -> b) -> c:Const m a -> cc:Const m c  @-}
constfmap :: (a -> b) -> Const m a -> Const m c
constfmap _ (Const a) = Const a

instance Functor (Const a) where
    fmap = constfmap

instance Functor (Identity) where
    fmap f (Identity a) = Identity (f a)

{-@ data Const a b = Const {unConst :: a} @-}
data Const a b = Const {unConst :: a}


{-@ reflect view @-}
view :: Lens s t a b -> s -> a
view lens s = unConst (lens Const s)


{-@ viewRef :: forall s <p :: s -> Bool> . ReLens <p> s s a a -> s<p> -> a @-}
viewRef :: ReLens s s a a -> s -> a
viewRef (ReLens lens) = view lens 

{-@ setRef :: forall s t a b <p :: s -> Bool> . lens:ReLens <p> s t a b -> val:b -> s<p> -> t @-}
setRef :: ReLens s t a b -> b -> s -> t
setRef (ReLens lens) b s = runIdentity (lens  (constIdentity b) s)

-- {-@ reflect set @-}
{-@ set :: lens:Lens s t a b -> v:b -> val:s -> {res:t | True} @-}
set :: Lens s t a b -> b -> s -> t
set lens b s = runIdentity (lens  (constIdentity b) s)

-- {-@ reflect over @-}
-- {-@ over :: lens:Lens s t a b -> v:b -> val:s -> res:t @-}
over :: Lens s t a b -> (a -> b) -> s -> t
over lens f s = runIdentity (lens (Identity . f) s)



{-@ refSet :: forall s t a b <p :: Int -> b -> Bool> . lens:Lens s t (x:a) b -> v:b<p 1> -> val:s -> res:t @-}
refSet :: Lens s t a b -> b -> s -> t
refSet lens b s = runIdentity (lens (constIdentity b) s)


{-@ data Identity a = Identity {runIdentity :: a} @-}
data Identity a = Identity {runIdentity :: a}


-- {-@ reflect constIdentity @-}
constIdentity :: a -> b -> Identity a
constIdentity a _ = Identity a

-- {-@ data D = A | B  @-}
data D = A | B deriving Show

type Lens' s a = Lens s s a a


{-@ data DPair = DPair {x :: Nat, y :: D} @-}
data DPair = DPair {x :: Int, y :: D} deriving Show

{-@ dpairFlipped :: D -> Nat -> DPair @-}
dpairFlipped :: D -> Int -> DPair
dpairFlipped y x = DPair x y

{-@  xLens :: Lens DPair DPair Nat Nat @-} 
xLens afb (DPair x y) = fmap (dpairFlipped y) (afb x)

dp = DPair 1 A

{-@ n :: Nat @-}
n = view xLens (DPair 1 A)

d1 = set xLens 2 (DPair 1 A)
d2 = over xLens (*2) (DPair 1 A)

{-@ data P = P {px :: DPair, py :: DPair} @-}
data P = P {px :: DPair, py :: DPair} deriving Show


{-@  pyLens :: Lens' P DPair @-} 
pyLens :: Lens' P DPair
pyLens afb (P x y) = fmap (P x) (afb y)

{-@  pyXLens :: Lens' P Nat @-} 
pyXLens :: Lens' P Int
pyXLens afb (P x (DPair x' y)) = fmap (P x . dpairFlipped y) (afb x')

{-@ noe :: Lens' P Nat @-}
noe :: Lens' P Int
noe = pyLens . xLens


s' = view noe (P dp dp)
s2 = view pyXLens (P dp dp)


{-@ ix :: i:Nat -> ReLens <{\x -> len x > i}> [a] [a] a a @-}
ix :: Int -> ReLens [a] [a] a a
ix n = ReLens (\afb xs -> let (pre,x,post) = split n xs in fmap (\y -> pre ++ y:post) (afb x))


{-@ split :: i:Nat -> {xs:[a] | len xs > i} -> ([a],a,[a]) @-}
split :: Int -> [a] -> ([a],a,[a])
split n xs = (pre,p,post)
    where
    (pre,p:post) = splitAt n xs


{-@ data ReLens s t a b  <p :: s -> Bool> = ReLens (Lens s<p> t<p> a b) @-}
data ReLens s t a b = ReLens {getReLens ::(Lens s t a b)}    

    

ixTest = viewRef (ix 0) [1,2,3::Int] 

-- Sadly it seems impossible at this time to make any reffinement to the return type
-- {-@ ixTest2 :: {v:[Integer] | len v == 3} @-}
ixTest2 = setRef (ix 1) 0 [1,2,3] 


--Not safe!
-- ixTest3 = viewRef (ix 5) [1,0,3]
-- ixTest4 = setRef (ix 10) 6 [1,0,3]
