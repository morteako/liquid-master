{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}

import Control.Lens
--type Traversal s t a b = forall f. Applicative f => (a -> f b) -> s -> f t


data Foo a = Foo {
    ints :: [Int],
    vals :: [a],
    marker :: Maybe a
} deriving Show


fooA :: Traversal (Foo a) (Foo b) a b
fooA afb s = Foo <$> pure (ints s) <*> vs <*> ms
    where
        vs = traverse afb $ vals s
        ms = traverse afb $ marker s

fooInts :: Traversal' (Foo a) Int
fooInts afb s = Foo <$> traverse afb (ints s) <*> pure (vals s) <*> pure (marker s)
        

foo = Foo [1..10] "heihomortenerkul" (Just 'a')


overO :: ((a -> Identity b) -> s -> Identity t) -> (a -> b) -> s -> t
overO setter f s = runIdentity $ setter (Identity . f) s

setO setter b s = over setter (const b) s

data HK f g h = HK {
    nums :: f Int,
    chars :: g Char,
    bools :: h Bool
} 

deriving instance (Show (f Int), Show (g Char), Show (h Bool)) => Show (HK f g h)

type (~>) f g = forall x. f x -> g x

type NatTrans f g ft = forall x. f x -> ft (g x)

type HKLens s t f g fa = forall func . Functor func => (NatTrans f g func) -> s -> func t

type HKTrans s t f g = (f ~> g) -> s -> t


fHKT :: HKTrans (HK f g h) (HK f' g h) f f'
fHKT natTrans (HK n c b) = HK (natTrans n) c b


fHK :: HKLens (HK Maybe g h) (HK [] g h) Maybe [] Int
fHK natTrans (HK n c b) = fmap (\x -> HK x c b) (natTrans n)

hk = HK {
    nums = Just 5,
    chars = "heiho",
    bools = Left True
}

-- constNatTrans :: NatTrans f g Const 
-- constNatTrans = Const 1

idNatTrans :: (f ~> g) -> NatTrans f g Identity
idNatTrans natTrans = Identity . natTrans



hkNatOver :: Functor f => HKLens s t f g a -> (f ~> g) -> s -> t
hkNatOver lens natTrans s = runIdentity $ lens (idNatTrans natTrans) s

-- hkView :: Functor f => HKLens s t f g a -> s -> f a
-- hkView lens s = unConst $ lens (idNatTrans natTrans) s


maybeToList :: Maybe ~> []
maybeToList Nothing = []
maybeToList (Just x) = [x]


main = do
    print ":)"
    print $ getConst $ fooA (Const . (:"")) foo
    print $ runIdentity $ fooA Identity foo
    print $ overO fooA show foo
    print $ setO fooA 'x' foo

    print hk
    print $ hkNatOver fHK maybeToList hk