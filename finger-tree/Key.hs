{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--ple" @-}

import Prelude hiding ( (<>), max)

import Liquid.Haskell.ProofCombinators (trivial, Proof)


data Key a = NoKey | Key a


{-@ reflect keyMempty @-}
keyMempty :: Key a
keyMempty = NoKey

{-@ infix <> @-}
{-@ reflect <> @-}
(<>) :: Ord a => Key a -> Key a -> Key a
k <> NoKey = k
_ <> k = k

{-@ mempty_proof :: Ord a => p:Key a -> { p <> keyMempty == p && keyMempty <> p == p }  @-}
mempty_proof :: Ord a => Key a -> Proof
mempty_proof _ = trivial

{-@ assoc_proof :: Ord a => x:Key a -> y:Key a -> z:Key a -> { x <> (y <> z) == (x <> y) <> z } @-}
assoc_proof :: Ord a => Key a -> Key a -> Key a -> Proof
assoc_proof _ _ _ = trivial