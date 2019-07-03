{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--no-adt"         @-}

{-@ LIQUID "--ple"            @-}

module FT where 

-- import Language.Haskell.Liquid.ProofCombinators 
import Proof 



-- data Digit a
--     = One a
--     | Two a a
--     | Three a a a
--     | Four a a a a
--     deriving (Show)
{-@ type Dig a = {v:[a] | len v >= 1 && len v <= 4} @-}
type Digit a = [a]

data Node a = Node2 {a2::a, b2::a} | Node3 {a3::a, b3::a, c3:: a}
    deriving (Show)

{-@ data FingerTree a = 
  Deep {lft::(Dig a) , mid::(FingerTree (Node a)), rft :: (Dig a)}
  | Single a
  |   Empty
@-}
data FingerTree a
    = Empty
    | Single a
    | Deep (Digit a) (FingerTree (Node a)) (Digit a)
    deriving Show

{-@ reflect fingerTreeSize @-}
fingerTreeSize :: FingerTree a -> Int
fingerTreeSize t = size to1 t 

{-@ reflect size @-}
size :: (a -> Int) -> FingerTree a -> Int
size _ Empty        = 0
size f (Single a)   = f a
size f (Deep l m r) = digitS f l + size (nodeS f) m + digitS f r

{-@ reflect digitS @-} 
{-@ digitS :: (a -> Int) -> Dig a -> Int @-}
digitS :: (a -> Int) -> Digit a -> Int
digitS f [a]        = f a
digitS f [a,b]      = f a + f b
digitS f [a,b,c]  = f a + f b + f c
digitS f [a,b,c,d] = f a + f b + f c + f d

{-@ reflect nodeS @-}
nodeS :: (a -> Int) -> Node a -> Int
nodeS f (Node2 a b)   = f a + f b
nodeS f (Node3 a b c) = f a + f b + f c


{-@ reflect to1 @-}
to1 :: a -> Int
to1 _ = 1

{-@ n2Int1 :: a:Int -> b:Int -> {n:Node Int | nodeS to1 n == 2} @-}
n2Int1 :: Int -> Int -> Node Int
n2Int1 a b = Node2 a b


-- {-@ measure isEmpty @-}
-- isEmpty Empty      = True
-- isEmpty (Single _) = False
-- isEmpty Deep{}     = False

-- {-@ singleton :: v:Int -> {ft:FingerTree Int | isEmpty ft} @-}
-- singleton :: Int -> FingerTree Int
-- singleton a = Empty 

{-@ fromList :: xs:_ -> {t:_ | fingerTreeSize t == len xs} @-}
fromList :: [a] -> FingerTree a
fromList []     = Empty
fromList (x:xs) = add x (fromList xs)

{-@ infix <| @-}
{-@ reflect <| @-}
(<|) :: a -> FingerTree a -> FingerTree a
a <| Empty                    =  Single a
a <| Single b                 =  Deep [a] Empty [b]
a <| Deep [b,c,d,e] m sf = Deep [a, b] (Node3 c d e <| m) sf
a <| Deep l m r               = Deep (consDigit a l) m r 


{-@ infix |> @-}
{-@ reflect |> @-}
(|>) ::FingerTree a -> a -> FingerTree a
Empty |> a              =  Single a
Single a |> b           =  Deep [a] Empty [b]
Deep pr m [a,b,c,d] |> e = 
    Deep pr (m |> Node3 a b c) [d, e]
Deep pr m sf |> x     =
    Deep pr m (snocDigit sf x)




{-@ lem_add_l :: f:_ -> a:_ -> t:_ -> { size f (a <| t) == size f t + f a }  @-}
lem_add_l :: (a -> Int) -> a -> FingerTree a -> () 
lem_add_l f _ Empty       
  = trivial 
lem_add_l f _ (Single {}) 
  = trivial 
lem_add_l f a t@(Deep [b,c,d,e] m sf) 
  =   size f t + f a 
  === digitS f [b,c,d,e] + size (nodeS f) m + digitS f sf + f a
  === f a + f b + digitS f sf + f c + f d + f e + size (nodeS f) m 
  === f a + f b + digitS f sf + nodeS f (Node3 c d e) + size (nodeS f) m 
      ? lem_add_l (nodeS f) (Node3 c d e) m
  === f a + f b + digitS f sf + size (nodeS f) ((Node3 c d e) <| m)
  === size f (Deep [a, b] (Node3 c d e <| m) sf)
  === size f (a <| (Deep [b,c,d,e] m sf)) 
  === size f (a <| t)
  *** QED  
lem_add_l f a t@(Deep l m r)  
  = trivial 

{-@ thm_add :: a:_ -> t:_ -> { fingerTreeSize (a <| t) == 1 + fingerTreeSize t} @-}
thm_add :: a -> FingerTree a -> Proof --  FingerTree a 
thm_add a t 
  =   fingerTreeSize (a <| t) 
  === size to1 (a <| t) 
    ? lem_add_l to1 a t
  === size to1 t + to1 a 
  === fingerTreeSize t + 1 
  *** QED

{-@ add :: a:_ -> t:_ -> { v: _ | fingerTreeSize v == 1 + fingerTreeSize t} @-}
add :: a -> FingerTree a -> FingerTree a 
add a t = (a <| t) ? thm_add a t 

{-@ add_r :: a:_ -> t:_ -> { v: _ | fingerTreeSize v == 1 + fingerTreeSize t} @-}
add_r :: a -> FingerTree a -> FingerTree a 
add_r a t = (t |> a) ? thm_add_r a t 

{-@ lazy un @-}
un = un

{-@ lem_add_r :: f:_ -> a:_ -> t:_ -> { size f (t |> a) == size f t + f a }  @-}
lem_add_r :: (a -> Int) -> a -> FingerTree a -> () 
lem_add_r f _ Empty       
  = trivial 
lem_add_r f _ (Single {}) 
  = trivial 
lem_add_r f x t@(Deep pr m [a,b,c,d]) 
  =   size f t + f x 
  === digitS f pr + size (nodeS f) m + digitS f [a,b,c,d] + f x
  === digitS f pr + size (nodeS f) m + f a +  f b + f c + f d + f x
  === digitS f pr + size (nodeS f) m + nodeS f (Node3 a b c) + f d + f x
      ? lem_add_r (nodeS f) (Node3 a b c) m
  === digitS f pr + size (nodeS f) (m |> Node3 a b c) + f d + f x
  === digitS f pr + size (nodeS f) (m |> Node3 a b c) + digitS f [d, x]
  === size f (Deep pr (m |> Node3 a b c) [d, x])
  === size f (Deep pr m [a,b,c,d] |> x) 
  === size f (t |> x)
  *** QED  
lem_add_r f a t@(Deep l m r)  
  = trivial 

{-@ thm_add_r :: a:_ -> t:_ -> { fingerTreeSize (t |> a) == 1 + fingerTreeSize t} @-}
thm_add_r :: a -> FingerTree a -> Proof --  FingerTree a 
thm_add_r a t 
  =   fingerTreeSize (t |> a) 
  === size to1 (t |> a) 
    ? lem_add_r to1 a t
  === size to1 t + to1 a 
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













{-@ ft1 :: {v:_ | fingerTreeSize v == 10} @-}
ft1 :: FingerTree Int
ft1 = fromList [1,2,3,4,5,6,7,8,9,10]

{-@ ten :: {v:_ | len v = 10} @-}
ten :: [Int]
ten = [1,2,3,4,5,6,7,8,9,10]

ft2 :: FingerTree Int
ft2 = fromList [1..20000]

main :: IO ()
main = do
    print "test"
    print $ fingerTreeSize ft1 -- 10
    print $ fingerTreeSize ft2 -- 20000