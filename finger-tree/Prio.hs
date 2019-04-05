{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--ple" @-}

import Prelude hiding ( (<>), max)

import Liquid.Haskell.ProofCombinators


data Prio a = MInfty | Prio a

{-@ reflect max @-}
max :: Ord a => a -> a -> a
max a b = if a > b then a else b

{-@ reflect prioMempty @-}
prioMempty :: Prio a
prioMempty = MInfty

{-@ infix <> @-}
{-@ reflect <> @-}
(<>) :: Ord a => Prio a -> Prio a -> Prio a
MInfty <> p = p
p <> MInfty = p
Prio m <> Prio n = Prio (max m n)

{-@ lazy un @-}
un = un

{-@ mempty_proof :: Ord a => p:Prio a -> { p <> prioMempty == p && prioMempty <> p == p }  @-}
mempty_proof :: Ord a => Prio a -> Proof
mempty_proof _ = trivial

{-@ assoc_proof :: Ord a => x:Prio a -> y:Prio a -> z:Prio a -> { x <> (y <> z) == (x <> y) <> z } @-}
assoc_proof :: Ord a => Prio a -> Prio a -> Prio a -> Proof
assoc_proof _ _ _ = trivial