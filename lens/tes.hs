{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--no-adt"     @-}

{-# LANGUAGE RankNTypes #-}

import Language.Liquid.Haskell.ProofCombinators

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
    fmap = idfmap

{-@ data Const a b = Const {unConst :: a} @-}
data Const a b = Const {unConst :: a}


{-@ reflect view @-}
view :: Lens s t a b -> s -> a
view lens s = unConst (lens Const s)

{-@ viewRef :: forall s <p :: s -> Bool> . ReLens <p> s t a b -> s<p> -> a @-}
viewRef :: ReLens s t a b -> s -> a
viewRef (ReLens lens) = view lens 

{-@ setRef :: forall s <p :: s -> Bool> . ReLens <p> s s a a -> a -> s<p> -> s<p> @-}
setRef :: ReLens s s b b -> b -> s -> s
setRef (ReLens lens) = set lens

-- {-@ reflect set @-}

-- {-@ set :: lens:Lens s t a b -> v:b -> s -> t @-}
set :: Lens s t a b -> b -> s -> t
set lens b s = runIdentity (lens  (constIdentity b) s)

{-@ assume set' :: lens:Lens s s a a -> v:a -> val:s -> { res:s | view lens res == v} @-}
set' :: Lens s s a a -> a -> s -> s
set' lens b s = runIdentity (lens  (constIdentity b) s)


-- {-@ reflect over @-}
-- {-@ over :: lens:Lens s t a b -> v:b -> val:s -> res:t @-}
over :: Lens s t a b -> (a -> b) -> s -> t
over lens f s = runIdentity (lens (Identity . f) s)



-- {-@ type ReLens s t a b <l :: a -> b -> Bool>  = Lens s t a b  @-}

{-@ data ReLens s t a b  <p :: s -> Bool> = ReLens (Lens s<p> t<p> a b) @-}
data ReLens s t a b = ReLens {getReLens ::(Lens s t a b)}    


-- {-@ r :: ReLens <{\a b -> a < b}> DPair DPair Nat Nat @-}
-- r = ReLens xLens


{-@ refSet :: forall s t a b <p :: Int -> b -> Bool> . lens:Lens s t (x:a) b -> v:b<p 1> -> val:s -> res:t @-}
refSet :: Lens s t a b -> b -> s -> t
refSet lens b s = runIdentity (lens (constIdentity b) s)


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

-- type Lens s t a b = forall f. (forall a b . (a -> b) -> f a -> f b) -> (a -> f b) -> s -> f t
type Lens' s a = Lens s s a a


{-@ data DPair = DPair {x :: Nat, y :: D} @-}
data DPair = DPair {x :: Int, y :: D} deriving Show

-- {-@ reflect dpairFlipped @-}
{-@ dpairFlipped :: D -> Nat -> DPair @-}
dpairFlipped :: D -> Int -> DPair
dpairFlipped y x = DPair x y

-- {-@ reflect xLens @-}
{-@  xLens :: Lens DPair DPair Nat Nat @-} 
-- xLens :: Lens' DPair Int
xLens afb (DPair x y) = fmap (dpairFlipped y) (afb x)

dp = DPair 1 A

-- {-@ reflect n @-}
{-@ n :: Nat @-}
n = view xLens (DPair 1 A)

d = set xLens 2 (DPair 1 A)

dd = refSet xLens 2 (DPair 1 A)

d2 = over xLens (*2) (DPair 1 A)

{-@ data P = P {px :: DPair, py :: DPair} @-}
data P = P {px :: DPair, py :: DPair} deriving Show

-- {-@ reflect pyLens @-}
{-@  pyLens :: Lens' P DPair @-} 
pyLens :: Lens' P DPair
pyLens afb (P x y) = fmap (P x) (afb y)

-- {-@ assume compose :: Lens' P DPair -> Lens' DPair Nat -> Lens' P Nat @-}
-- compose :: Lens' P DPair -> Lens' DPair Int -> Lens' P Int 
-- compose f g x = f (g x)

-- {-@ assume comp :: forall s a x <p :: x -> Bool> . Lens' s a -> Lens' a x<p> -> Lens' s x<p> @-}
-- -- comp :: Lens' P DPair -> Lens' DPair Int -> Lens' P Int
-- comp :: Lens' s a -> Lens' a x -> Lens' s x 
-- comp f g = f . g

{-@  pyXLens :: Lens' P Nat @-} 
pyXLens :: Lens' P Int
pyXLens afb (P x (DPair x' y)) = fmap (P x . dpairFlipped y) (afb x')

{-@ noe :: Lens' P Nat @-}
noe :: Lens' P Int
noe = pyLens . xLens

-- s = view (compose pyLens xLens) (P dp dp)
s' = view noe (P dp dp)
-- s'' = view (pyLens . xLens) (P dp dp)
s2 = view (pyXLens) (P dp dp)


-- {-@ ix1 :: {i:Int | i == 0] -> Lens [a] [b] a b} @-}
-- ix1 :: Int -> Lens [a] [b] a b
-- ix1 i afb 

{-@ ix :: i:Nat -> ReLens <{\x -> len x > i}> [a] [a] a a @-}
ix :: Int -> ReLens [a] [a] a a
ix n = ReLens (func n)
    where
        {-@ assume func :: forall f . Functor f => i:Nat -> (a -> f a) -> {xs:[a] | len xs > i} -> ys:f {v:[a] | len v == len xs} @-}
        func n afb xs = let (pre,x,post) = split n xs in fmap (\y -> pre ++ y:post) (afb x)


{-@ assume split :: i:Nat -> {xs:[a] | len xs > i} -> ([a],a,[a]) @-}
split :: Int -> [a] -> ([a],a,[a])
split n xs = (pre,p,post)
    where
    (pre,p:post) = splitAt n xs

ixTest = viewRef (ix 0) [1,2,3] 

-- {-@ ixTest2 :: {v:[Integer] | len v == 3} @-}
ixTest2 = setRef (ix 1) 0 [1,2,3] 

{-@ ss :: {v : Int | v == 1} @-}
ss = view xLens (set' xLens 1 (DPair 2 A))
