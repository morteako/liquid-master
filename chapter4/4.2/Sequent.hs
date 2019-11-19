{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

import GHC.TypeLits
import Data.Type.Bool

data F a = 
        V a           --Var
    |   A (F a) (F a) --And
    |   N (F a)       --Not
    |   O (F a) (F a) --Or
    |   I (F a) (F a) --Impl

data Formula s where
    Var :: (KnownNat n) => Formula (V n)
    Not :: Formula q -> Formula (N q)
    And :: Formula q -> Formula u -> Formula (A q u)
    Or  :: Formula q -> Formula u -> Formula (O q u)
    Impl:: Formula q -> Formula u -> Formula (I q u)

data Seq = Side :=> Side

data Side = Side [F Nat] [Nat]

type family AnyOverlap (xs :: [Nat]) (ys :: [Nat]) where
    AnyOverlap '[] ys      = 'False
    AnyOverlap (x : xs) ys = Find x ys || AnyOverlap xs ys
    
type family Find (x :: Nat) (xs :: [Nat]) where
    Find x '[]       = 'False
    Find x (x : ys) = 'True
    Find x (y : ys) = Find x ys

type family Sequent (s :: Seq )  where
    Sequent ('Side '[] avars :=> 'Side '[] bvars) = 
        AnyOverlap avars bvars

    --Left logical rules
    Sequent ('Side (V n : as) avars :=> right) = 
        Sequent ('Side as (n : avars) :=> right)
    Sequent ('Side (N fm : as) avars :=> 'Side bs bvars) = 
        Sequent ('Side as avars :=> 'Side (fm : bs) bvars)
    Sequent ('Side (A l r : as) avars :=> right) = 
        Sequent ('Side (l : r : as) avars :=> right) 
    Sequent ('Side (O l r : as) avars :=> right) = 
        Sequent ('Side (l : as) avars :=> right) 
        &&
        Sequent ('Side (r : as) avars :=> right) 
    Sequent ('Side (I a b : as) avars :=> ('Side bs bvars)) = 
        Sequent ('Side as avars :=> 'Side (a:bs) bvars) 
        &&
        Sequent ('Side (b:as) avars :=> 'Side bs bvars)

    --Right logical rules
    Sequent ('Side as avars :=> 'Side (I a b : bs) bvars) = 
        Sequent ('Side (a:as) avars :=> 'Side (b:bs) bvars)
    Sequent (left :=> 'Side (V n : b) bvars) = 
        Sequent (left :=> 'Side b (n:bvars))
    Sequent (left :=> 'Side (A l r : b) bvars) = 
        Sequent (left :=> 'Side (l:b) bvars) && Sequent (left :=> 'Side (r:b) bvars)
    Sequent (left :=> 'Side (O l r : b) bvars) = 
        Sequent (left :=> 'Side (l:r:b) bvars)
    Sequent ('Side as avars :=> 'Side (N fm : bs) bvars) = 
        Sequent ('Side (fm : as) avars :=> 'Side bs bvars)


data IsTheorem = Theo | NonTheo

type family CheckTheo fm where
    CheckTheo fm = If (Sequent ('Side '[] '[] :=> 'Side '[fm] '[])) Theo NonTheo

data Theorem (fm :: F Nat) where
    Theorem :: (CheckTheo fm ~ Theo) => Formula fm -> Theorem fm

p1 :: Formula (V 1)
p1 = Var

-- not (p1 && not p1 )
theo1 = Theorem $ Not $ And p1 (Not p1)

-- p1 -> p1
theo2 = Theorem $ Impl p1 p1

-- will not type check
-- p1 && not p1
--nonTheo1 = Theorem $ And (Var @1) (Not (Var @1))
