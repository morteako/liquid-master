import Proof

{-@ lazy repeatValue @-}
{-@ repeatValue :: a -> {v:[a] | len v >= 5} @-}
repeatValue a = a : repeatValue a

{-@ o :: {v:[{e:_ | e == 1}] | len v == 5} @-}
o = take 5 (repeatValue 1)

{-@ lazy repeatValueBad @-}
{-@ repeatValueBad :: a -> {v:[a] | True == False} @-}
repeatValueBad a = a : repeatValueBad a

{-@ lazy repeatNat @-}
{-@ repeatNat :: n:Nat -> {v:[Nat] | n == 2} @-}
repeatNat :: Int -> [Int]
repeatNat a = a : repeatNat a

{-@ p :: n:Nat -> {v:Nat | v == n && n == 2} @-}
p n = n ? repeatNat n

{-@ f :: {v:Nat | v == 2} -> () @-}
f :: Int -> ()
f 2 = ()

runFwith3 = f (p 3) 
