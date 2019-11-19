{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--no-adt"         @-}
{-@ LIQUID "--ple"            @-}

module FTsizeRight where 

import Proof 
import FTsizeLeft hiding (fromList)



{-@ infix |> @-}
{-@ reflect |> @-}
(|>) ::FingerTree a -> a -> FingerTree a
Empty |> a              =  Single a
Single a |> b           =  Deep [a] Empty [b]
Deep pr m [a,b,c,d] |> e = 
    Deep pr (m |> Node3 a b c) [d, e]
Deep pr m sf |> x     =
    Deep pr m (snocDigit sf x)


{-@ addRight :: a:_ -> t:_ -> { v: _ | fingerTreeSize v == 1 + fingerTreeSize t} @-}
addRight :: a -> FingerTree a -> FingerTree a 
addRight a t = (t |> a) ? thm_add_r a t 


{-@ lem_add_r :: f:_ -> a:_ -> t:_ -> { ftSizeGen f (t |> a) == ftSizeGen f t + f a }  @-}
lem_add_r :: (a -> Int) -> a -> FingerTree a -> () 
lem_add_r f _ Empty       
  = trivial 
lem_add_r f _ (Single {}) 
  = trivial 
lem_add_r f x t@(Deep pr m [a,b,c,d]) 
  =   ftSizeGen f t + f x 
  === digitS f pr + ftSizeGen (nodeS f) m + digitS f [a,b,c,d] + f x
  === digitS f pr + ftSizeGen (nodeS f) m + f a +  f b + f c + f d + f x
  === digitS f pr + ftSizeGen (nodeS f) m + nodeS f (Node3 a b c) + f d + f x
      ? lem_add_r (nodeS f) (Node3 a b c) m
  === digitS f pr + ftSizeGen (nodeS f) (m |> Node3 a b c) + f d + f x
  === digitS f pr + ftSizeGen (nodeS f) (m |> Node3 a b c) + digitS f [d, x]
  === ftSizeGen f (Deep pr (m |> Node3 a b c) [d, x])
  === ftSizeGen f (Deep pr m [a,b,c,d] |> x) 
  === ftSizeGen f (t |> x)
  *** QED  
lem_add_r f a t@(Deep l m r)  
  = trivial 

{-@ thm_add_r :: a:_ -> t:_ -> { fingerTreeSize (t |> a) == 1 + fingerTreeSize t} @-}
thm_add_r :: a -> FingerTree a -> Proof --  FingerTree a 
thm_add_r a t 
  =   fingerTreeSize (t |> a) 
  === ftSizeGen to1 (t |> a) 
    ? lem_add_r to1 a t
  === ftSizeGen to1 t + to1 a 
  === fingerTreeSize t + 1 
  *** QED


{-@ reflect consDigit @-}
{-@ consDigit :: _ -> {d:Dig a | len d < 4} -> _ @-}
consDigit :: a -> Digit a -> Digit a
consDigit x [a] = [x,a]
consDigit x [a,b] = [x,a,b]
consDigit x [a,b,c] = [x,a,b,c]

{-@ reflect snocDigit @-}
{-@ snocDigit :: {d:Dig a | len d < 4} -> v:a -> {dd : Digit a | len dd == len d + 1} @-}
snocDigit :: Digit a -> a -> Digit a
snocDigit [a] x = [a,x]
snocDigit [a,b] x = [a,b,x]
snocDigit [a,b,c] x = [a,b,c,x]

{-@ fromList :: xs:_ -> {t:_ | fingerTreeSize t == len xs} @-}
fromList :: [a] -> FingerTree a
fromList []     = Empty
fromList (x:xs) = addRight x (fromList xs)

{-@ ft2 :: {v:_ | fingerTreeSize v == 10} @-}
ft2 :: FingerTree Int
ft2 = fromList [1,2,3,4,5,6,7,8,9,10]
