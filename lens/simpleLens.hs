{-@ LIQUID "--ple" @-}
{-@ LIQUID "--no-adt"         @-}
{-@ LIQUID "--reflection"     @-}

import Language.Liquid.Haskell.ProofCombinators
-- LENS

{-@ data L s a = L { lset :: s -> a -> s, lget :: s -> a } @-}
data L s a = L { lset :: s -> a -> s, lget :: s -> a }

{-@ reflect set @-}
set :: L s a -> a -> s -> s
set lens a s = lset lens s a 

{-@ reflect view @-}
view :: L s a -> s -> a
view lens s = lget lens s

{-@ safeView :: lens: L s a -> s:s -> proof:(v:a -> {p:Proof | view lens (set lens v s) == v }) -> res:a @-}
safeView :: L s a -> s -> (a -> Proof) -> a
safeView lens s proof = view lens s


-- Example

{-@ data Pair = Pair {left::Bool, right :: Bool} @-}
data Pair = Pair Bool Bool

{-@ reflect leftLens @-}
leftLens :: L Pair Bool
leftLens = L leftSet leftGet

{-@ reflect leftSet @-}
leftSet :: Pair -> Bool -> Pair
leftSet (Pair _ r) l = Pair l r

{-@ reflect leftGet @-}
leftGet :: Pair -> Bool
leftGet (Pair l _) = l

{-@ leftLens_1 :: v:Bool-> s:Pair -> { view leftLens (set leftLens v s) == v}  @-}
leftLens_1 :: Bool-> Pair -> Proof
leftLens_1 i s@(Pair xx yy)
    = trivial

{-@ leftLens_2 :: s:Pair -> { set leftLens (view leftLens s) s == s}  @-}
leftLens_2 :: Pair -> Proof
leftLens_2  s@(Pair xx yy) = trivial

{-@ leftLens_3 :: v:Bool-> vv:Bool-> s:Pair -> { set leftLens vv (set leftLens v s) == set leftLens vv s }  @-}
leftLens_3 :: Bool -> Bool -> Pair -> Proof
leftLens_3 _ _ _ = trivial

{-@ p :: {b:Bool | b == True } @-}
p = view leftLens (set leftLens True (Pair False False)) ? leftLens_1 True (Pair False False)
