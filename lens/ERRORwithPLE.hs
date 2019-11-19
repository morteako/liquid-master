-- {-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--no-adt"     @-}

{-# LANGUAGE RankNTypes #-}

import Language.Liquid.Haskell.ProofCombinators

{-@ reflect un @-}
{-@ lazy un @-}
un = un

type FLens s t a b = forall f. (forall a b . (a -> b) -> f a -> f b) -> (a -> f b) -> s -> f t


{-@ reflect constfmap @-}
{-@ constfmap :: f:(a -> b) -> c:Const m a -> cc:Const m c  @-}
constfmap :: (a -> b) -> Const m a -> Const m c
constfmap _ (Const a) = Const a


{-@ data Const a b = Const {unConst :: a} @-}
data Const a b = Const {unConst :: a}


{-@ reflect view @-}
view :: FLens s t a b -> s -> a
view lens s = unConst (lens constfmap Const s)


{-@ reflect set @-}
{-@ set :: lens:FLens s t a b -> v:b -> val:s -> res:t @-}
set :: FLens s t a b -> b -> s -> t
set lens b s = runIdentity (lens idfmap (constIdentity b) s)


-- {-@ reflect over @-}
-- {-@ over :: lens:FLens s t a b -> v:b -> val:s -> res:t @-}
over :: FLens s t a b -> (a -> b) -> s -> t
over lens f s = runIdentity (lens idfmap (Identity . f) s)



-- {-@ type RefLens s t a b <l :: a -> b -> Bool>  = FLens s t a b  @-}

{-@ data RefLens s t a b  <l :: a -> b -> Bool> = RefLens (FLens s t a b) @-}
data RefLens s t a b = RefLens (FLens s t a b)    


{-@ r :: RefLens <{\a b -> a < b}> DPair DPair Nat Nat @-}
r = RefLens xLens


{-@ refSet :: forall s t a b <p :: Int -> b -> Bool> . lens:FLens s t (x:a) b -> v:b<p n> -> val:s -> res:t @-}
refSet :: FLens s t a b -> b -> s -> t
refSet lens b s = runIdentity (lens idfmap (constIdentity b) s)


{-@ data Identity a = Identity {runIdentity :: a} @-}
data Identity a = Identity {runIdentity :: a}

{-@ reflect idfmap @-}
{-@ idfmap :: f:(a -> b) -> ia:Identity a -> ib:Identity b @-}
idfmap :: (a -> b) -> Identity a -> Identity b
idfmap f (Identity a) = Identity (f a)

{-@ reflect constIdentity @-}
{-@ constIdentity :: x:a -> v:b -> r:Identity a @-}
constIdentity :: a -> b -> Identity a
constIdentity a _ = Identity a

-- {-@ data D = A | B  @-}
data D = A | B deriving Show

-- type FLens s t a b = forall f. (forall a b . (a -> b) -> f a -> f b) -> (a -> f b) -> s -> f t
type FLens' s a = FLens s s a a

{-@ data DPair = DPair {x :: Nat, y :: D} @-}
data DPair = DPair {x :: Int, y :: D} deriving Show

{-@ reflect dpairFlipped @-}
{-@ dpairFlipped :: D -> Nat -> DPair @-}
dpairFlipped :: D -> Int -> DPair
dpairFlipped y x = DPair x y

{-@ reflect xLens @-}
{-@  xLens :: FLens' DPair Nat @-} 
xLens :: FLens' DPair Int
xLens fmap afb (DPair x y) = fmap (dpairFlipped y) (afb x)

{-@ reflect n @-}
{-@ n :: Nat @-}
n = view xLens (DPair 1 A)

d = set xLens 2 (DPair 1 A)

d2 = over xLens (*2) (DPair 1 A)

