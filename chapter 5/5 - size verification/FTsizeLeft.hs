{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--no-adt"         @-}
{-@ LIQUID "--ple"            @-}

module FTsizeLeft where 

import Proof

{-@ type Dig a = {v:[a] | len v >= 1 && len v <= 4} @-}
type Digit a = [a]

data Node a = Node2 a a | Node3 a a a

{-@ data FingerTree a = 
  Deep {
      lft::(Dig a) , 
      mid::(FingerTree (Node a)), 
      rft :: (Dig a)
  }
  | Single a
  |   Empty
@-}
data FingerTree a
    = Empty
    | Single a
    | Deep (Digit a) (FingerTree (Node a)) (Digit a)

{-@ reflect fingerTreeSize @-}
fingerTreeSize :: FingerTree a -> Int
fingerTreeSize t = ftSizeGen to1 t 

{-@ reflect ftSizeGen @-}
ftSizeGen :: 
    (a -> Int) -> FingerTree a -> Int
ftSizeGen _ Empty        = 0
ftSizeGen f (Single a)   = f a
ftSizeGen f (Deep l m r) = 
    digitS f l + ftSizeGen (nodeS f) m + digitS f r

{-@ reflect digitS @-} 
{-@ digitS :: (a -> Int) -> Dig a -> Int @-}
digitS :: (a -> Int) -> Digit a -> Int
digitS f [a]        = f a
digitS f [a,b]      = f a + f b
digitS f [a,b,c]    = f a + f b + f c
digitS f [a,b,c,d]  = f a + f b + f c + f d

{-@ reflect nodeS @-}
nodeS :: (a -> Int) -> Node a -> Int
nodeS f (Node2 a b)   = f a + f b
nodeS f (Node3 a b c) = f a + f b + f c

{-@ reflect to1 @-}
to1 :: a -> Int
to1 _ = 1


{-@ infix <| @-}
{-@ reflect <| @-}
(<|) :: a -> FingerTree a -> FingerTree a
a <| Empty                    = 
    Single a
a <| Single b                 = 
    Deep [a] Empty [b]
a <| Deep [b,c,d,e] m sf      = 
    Deep [a, b] (Node3 c d e <| m) sf
a <| Deep l m r               =
    Deep (consDigit a l) m r 

{-@ reflect consDigit @-}
{-@ consDigit :: _ -> {d:Dig a | len d < 4} -> _ @-}
consDigit :: a -> Digit a -> Digit a
consDigit x [a]     = [x,a]
consDigit x [a,b]   = [x,a,b]
consDigit x [a,b,c] = [x,a,b,c]


{-@ lem_add_l_gen :: 
    f:(a -> Int) -> a:a -> t:FingerTree a -> 
        { ftSizeGen f (a <| t) == ftSizeGen f t + f a }  
@-}
lem_add_l_gen :: (a -> Int) -> a -> FingerTree a -> () 
lem_add_l_gen f _ Empty       
  = trivial 
lem_add_l_gen f _ (Single {}) 
  = trivial 
lem_add_l_gen f a t@(Deep [b,c,d,e] m sf) 
  =   ftSizeGen f t + f a 
  === digitS f [b,c,d,e] + ftSizeGen (nodeS f) m + digitS f sf + f a
  === f a + f b + digitS f sf + f c + f d + f e + ftSizeGen (nodeS f) m 
  === f a + f b + digitS f sf + nodeS f (Node3 c d e) + ftSizeGen (nodeS f) m 
        ? lem_add_l_gen (nodeS f) (Node3 c d e) m
  === f a + f b + digitS f sf + ftSizeGen (nodeS f) ((Node3 c d e) <| m)
  === ftSizeGen f (Deep [a, b] (Node3 c d e <| m) sf)
  === ftSizeGen f (a <| (Deep [b,c,d,e] m sf)) 
  === ftSizeGen f (a <| t)
  *** QED  
lem_add_l_gen f a t@(Deep l m r)  
  = trivial 

{-@ lem_add_l :: a:_ -> t:_ -> { fingerTreeSize (a <| t) == 1 + fingerTreeSize t} @-}
lem_add_l :: a -> FingerTree a -> Proof
lem_add_l a t
  =   fingerTreeSize (a <| t) 
  === ftSizeGen to1 (a <| t) 
        ? lem_add_l_gen to1 a t
  === ftSizeGen to1 t + to1 a 
  === fingerTreeSize t + 1 
  *** QED

--Verified wrapper around <|
{-@ addLeft :: a:_ -> t:_ -> { v: _ | fingerTreeSize v == 1 + fingerTreeSize t} @-}
addLeft :: a -> FingerTree a -> FingerTree a 
addLeft a t = (a <| t) ? lem_add_l a t 


{-@ fromList :: xs:_ -> 
  {t:_ | fingerTreeSize t == len xs} @-}
fromList :: [a] -> FingerTree a
fromList []     = Empty
fromList (x:xs) = addLeft x (fromList xs)

{-@ ft1 :: {v:_ | fingerTreeSize v == 10} @-}
ft1 :: FingerTree Int
ft1 = fromList [1,2,3,4,5,6,7,8,9,10]