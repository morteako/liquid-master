{-# OPTIONS -w -WError -fwarn-incomplete-patterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}

import Data.Proxy
import Data.Type.Equality

data Nat = Z | S Nat

data Peano (n :: Nat) where
    Zero :: Peano Z
    Succ :: Peano n -> Peano (S n)

type family ((a::Nat) + (b::Nat)) :: Nat where
    Z + n = n
    (S n) + m = S (n + m)

cong :: forall k1 k2 (a :: k2) (b :: k2) (f :: k2 -> k1) .
    (a :~: b) -> f a :~: f b
cong Refl = Refl

rightId :: Peano n -> n :~: (n + Z)
rightId Zero = Refl
rightId (Succ s) = cong (rightId s) 

addSucc :: Peano n -> Peano m ->  (S n + m) :~: (n + S m)
addSucc Zero m = Refl
addSucc (Succ n) m = cong (addSucc n m)

plusComm :: Peano n -> Peano m -> (n+m) :~: (m+n)
plusComm Zero m
    =   rightId m 
plusComm (Succ n) m
    =    cong (plusComm n m) `trans` addSucc m n