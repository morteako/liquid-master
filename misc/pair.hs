{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--exactdc"         @-}
{-@ LIQUID "--trust-internals" @-}
{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}

import Language.Haskell.Liquid.ProofCombinators

data Pair a = Nil | Cons a (Pair a) | Comp (Pair a) (Pair a)

{-@ data Pair [psize] a = Nil | Cons {x::a,xs:: (Pair a)} | Comp {p::(Pair a) ,p'::(Pair a)} @-}

{-@ measure psize @-}
{-@ lazy psize @-}
{-@ psize :: Pair a -> {v:Int | v >= 0} @-}
psize :: Pair a -> Int
psize Nil = 0
psize (Cons a p) = 1 + psize p
psize (Comp p p') = 1 + psize p + psize p'

{-@ reflect ide @-}
{-@ ide :: v:a -> {w:a | v == w} @-}
ide :: a -> a
ide x = x


{-@ reflect pmap @-}
{-@ pmap :: (a->b) -> xs:Pair a -> {ys:Pair b | psize xs == psize ys}  / [psize xs] @-}
pmap :: (a->b) -> Pair a -> Pair b
pmap f Nil = Nil
pmap f (Cons a p) = Cons (f a) (pmap f p)
pmap f (Comp p p') = Comp (pmap f p) (pmap f p')

{-@ pmapId :: xs: Pair a -> {pmap ide xs == xs} @-}
pmapId :: Pair a -> ()
pmapId Nil =
  pmap ide Nil ==.
  ide Nil ==.
  Nil *** QED
pmapId (Cons x p) =
  pmap ide (Cons x p) ==.
  Cons (ide x) (pmap ide p) ==.
  Cons x (pmap ide p) ∵ pmapId p ==.
  Cons x p *** QED
pmapId (Comp p p') =
  pmap ide (Comp p p') ==.
  Comp (pmap ide p) (pmap ide p') ∵ pmapId p ==.
  Comp p (pmap ide p') ∵ pmapId p'  *** QED

{-@ reflect comp @-}
{-@ comp :: (b->c) -> (a->b) -> a->c @-}
comp :: (b->c) -> (a->b) -> a->c
comp f g x = f (g x)

{-@ pmapComp ::
xs:Pair a ->
f:(b->c) ->
g:(a->b) ->
{ (pmap f (pmap g xs)) == pmap (comp f g) xs}  @-}
pmapComp :: Pair a -> (b->c) -> (a->b) -> ()
pmapComp Nil f g =
  pmap f (pmap g Nil) ==. pmap f Nil ==. Nil ==.
  pmap (comp f g) Nil  *** QED
pmapComp (Cons x p) f g =
  pmap f (pmap g (Cons x p)) ==.
  pmap f (Cons (g x) (pmap g p)) ==.
  Cons (f (g x)) (pmap f (pmap g p)) ∵ pmapComp p f g ==.
  Cons (f (g x))      (pmap (comp f g) p) ==.
  Cons ((comp f g) x) (pmap (comp f g) p) ==.
  pmap (comp f g) (Cons x p) *** QED
pmapComp (Comp p p') f g =
  pmap f (pmap g (Comp p p')) ==.
  pmap f (Comp (pmap g p) (pmap g p')) ==.
  Comp (pmap f (pmap g p)) (pmap f (pmap g p'))  ∵ pmapComp p f g ==.
  Comp (pmap (comp f g) p) (pmap f (pmap g p'))  ∵ pmapComp p' f g ==.
  Comp (pmap (comp f g) p) (pmap (comp f g) p') ==.
  pmap (comp f g) (Comp p p') *** QED

{-@ reflect preturn @-}
preturn a = Cons a Nil

{-@ reflect appendPair @-}
appendPair Nil p = p
appendPair (Cons a p) p2 = Cons a (appendPair p p2)
appendPair (Comp p1 p2) p3 = Comp (appendPair p1 p3) p2

{-@ reflect concatPair @-}
concatPair Nil = Nil
concatPair (Cons p1 p2) = appendPair p1 (concatPair p2)
concatPair (Comp p1 p2) = Comp (concatPair p1) (concatPair p2)

{-@ reflect pbind @-}
pbind :: Pair a -> (a -> Pair b) -> Pair b
pbind p f = concatPair (pmap f p)

--pbind Nil f = Nil
--pbind (Cons a p) f = 


{-|
pbind (preturn a) f ==.
  pbind (Cons a Nil) f ==.
  concatPair (pmap f (Cons a Nil)) ==.
  concatPair (Cons (f a) Nil) ==.
  Cons (f a) Nil ==.
  f a  ***  QED
 |-}

{-@ leftId :: v:a -> f:(a->Pair b) -> {pbind (preturn v) f = f v}  @-}
leftId :: a -> (a->Pair b) -> Proof
leftId a f =
  undefined
  

{-@ rightId :: ma:Pair a -> {pbind ma preturn = ma}@-}
rightId :: Pair a -> Proof
rightId Nil =
  pbind Nil preturn ==.
  concatPair (pmap preturn Nil) ==.
  concatPair Nil ==.
  Nil *** QED
rightId (Cons a p) =
  pbind (Cons a p) preturn ==.
  concatPair (pmap preturn (Cons a p)) ==.
  concatPair (Cons (preturn a) (pmap preturn p)) ==.
  concatPair (Cons (Cons a Nil) (pmap preturn p)) ==.
  appendPair (Cons a Nil) (concatPair (pmap preturn p)) ==.
  Cons a (concatPair (pmap preturn p)) ==.
  Cons a (pbind p preturn) ∵ rightId p ==.
  --Cons a p *** QED
  undefined *** QED
rightId (Comp p1 p2) = undefined
  pbind (Comp p1 p2) preturn ==.
  concatPair (pmap preturn (Comp p1 p2)) ==.
  concatPair (Comp (pmap preturn p1) (pmap preturn p2)) ==.
  Comp (concatPair (pmap preturn p1)) (concatPair (pmap preturn p2)) ∵ rightId p1 ==.
  Comp p1 (concatPair (pmap preturn p2)) ∵ rightId p2 ==.
  Comp p1 p2 *** QED
  


  
  
  
{-|



|-}
  
