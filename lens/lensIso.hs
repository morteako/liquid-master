{-@ LIQUID "--ple" @-}
{-@ LIQUID "--no-adt"         @-}
{-@ LIQUID "--reflection"     @-}

{-# LANGUAGE RankNTypes #-}

import Language.Liquid.Haskell.ProofCombinators

{-@ reflect un @-}
{-@ lazy un @-}
un = un

type FLens s t a b = forall f. (forall a b . (a -> b) -> f a -> f b) -> (a -> f b) -> s -> f t

{-@ data SetGet s t a b = SetGet { _set :: s -> b -> t, _get :: s -> a } @-}
data SetGet s t a b = SetGet { _set :: s -> b -> t, _get :: s -> a }

{-@ toLens_set_iso :: Eq t => setGet : SetGet s t a b -> s:s -> b:b -> { set (setGetToLens setGet) b s == setSetGet setGet b s } @-}
toLens_set_iso :: Eq t => SetGet s t a b -> s -> b -> Proof
toLens_set_iso setGet s b = trivial

toLens_set_iso' :: Eq t => SetGet s t a b -> s -> b -> Bool
toLens_set_iso' setGet s b = set (setGetToLens setGet) b s == setSetGet setGet b s

{-@ reflect lensToSetGet @-}
lensToSetGet :: FLens s t a b -> SetGet s t a b
lensToSetGet lens = SetGet setter getter
    where
        setter s b = set lens b s
        getter = view lens

{-@ reflect setGetToLens  @-}
{-@ setGetToLens :: setGet:SetGet s t a b -> lens:FLens s t a b @-}
setGetToLens :: SetGet s t a b -> FLens s t a b
setGetToLens (SetGet setter getter) f afb s = f (setter s) $ afb (getter s)



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

{-@ reflect viewSetGet @-}
viewSetGet :: SetGet s t a b -> s -> a
viewSetGet (SetGet _ getter) s = getter s


{-@ reflect setSetGet @-}
{-@ setSetGet :: lens:SetGet s t a b -> v:b -> val:s -> res:t @-}
setSetGet :: SetGet s t a b -> b -> s -> t
setSetGet (SetGet setter _) b s = setter s b

    
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