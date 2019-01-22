{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--no-adt"         @-}   -- Tells LH to NOT embed `FingerTree` natively to SMT (since SMT can't handle polymorphic recursion)
{-@ LIQUID "--ple"            @-}   -- Enables "logical evaluation", a method for "type-level computation" with the reflected functions

-- Can't find ProofCombinators
--import Liquid.Haskell.ProofCombinators 
import ProofComb


{-@ measure digitSize @-}
digitSize :: Digit a -> Int
digitSize One{}    = 1
digitSize Two{}    = 2
digitSize Three{}  = 3
digitSize Four{}  = 4

data Digit a
    = One a
    | Two a a
    | Three a a a
    | Four a a a a
    deriving (Show)

data Node a = Node2 {a2::a, b2::a} | Node3 {a3::a, b3::a, c3:: a}
    deriving (Show)

data FingerTree a
    = Empty
    | Single a
    | Deep (Digit a) (FingerTree (Node a)) (Digit a)
    deriving Show


{-@ type FT a N = {ft:FingerTree a | fingerTreeSize ft == N } @-}

{-@ reflect fingerTreeSize @-}
fingerTreeSize :: FingerTree a -> Int
fingerTreeSize t = size to1 t 

{-@ reflect size @-}
size :: (a -> Int) -> FingerTree a -> Int
size _ Empty = 0
size f (Single a) = f a
size f (Deep l m r) = digitS f l + size (nodeS f) m + digitS f r

{-@ reflect digitS @-} 
digitS :: (a -> Int) -> Digit a -> Int
digitS f (One a) = f a
digitS f (Two a b) = f a + f b
digitS f (Three a b c) = f a + f b + f c
digitS f (Four a b c d) = f a + f b + f c + f d

{-@ reflect nodeS @-}
nodeS :: (a -> Int) -> Node a -> Int
nodeS f (Node2 a b)   = f a + f b
nodeS f (Node3 a b c) = f a + f b + f c

{-@ reflect to1 @-}
to1 :: a -> Int
to1 _ = 1

{-@ empty :: ft : FT a 0 @-}
empty :: FingerTree a
empty = Empty

{-@ measure isEmpty @-}
isEmpty Empty = True
isEmpty (Single _) = False
isEmpty Deep{} = False

{-@ singleton :: a -> FT a 1 @-}
singleton :: a -> FingerTree a
singleton a = Single a


{-@ fromList :: xs:[a] -> {ft : FingerTree a | fingerTreeSize ft == len xs} @-}
fromList :: [a] -> FingerTree a
fromList xs = from xs ? lem_from xs


{-@ reflect from @-}
{-@ from :: xs:[a] -> FingerTree a @-}
from :: [a] -> FingerTree a
from []     = Empty
from (x:xs) = x <| from xs

{-@ lem_from :: xs:[a] -> { len xs == fingerTreeSize (from xs) } @-}
lem_from :: [a]  -> Proof
lem_from [] = trivial
lem_from (x:xs) = lem_add_to1 x (from xs) &&& lem_from xs


(<|) :: a -> FingerTree a -> FingerTree a
a <| Empty              =  Single a
a <| Single b           =  Deep (One a) Empty (One b)
a <| Deep (Four b c d e) m sf = Deep (Two a b) (Node3 c d e <| m) sf
a <| Deep pr m sf     =
    Deep (consDigit a pr) m sf
{-@ infix <| @-}
{-@ reflect <| @-}

{-@ reflect consDigit @-}
{-@ consDigit :: v:a -> {d:Digit a | digitSize d < 4} -> {dd : Digit a | digitSize dd == digitSize d + 1} @-}
consDigit :: a -> Digit a -> Digit a
consDigit a (One b) = Two a b
consDigit a (Two b c) = Three a b c
consDigit a (Three b c d) = Four a b c d

{-@ lem_add_to1 ::  x:a -> t:FingerTree a -> { size to1 (x <| t) == size to1 t + to1 x }  @-}
lem_add_to1 :: a -> FingerTree a -> Proof
lem_add_to1 a t = lem_add to1 a t

{-@ lem_add :: f:(a -> Int) -> x:a -> t:FingerTree a -> { size f (x <| t) == size f t + f x }  @-}
lem_add :: (a -> Int) -> a -> FingerTree a -> Proof
lem_add f a Empty = trivial
lem_add f a (Single _) = trivial
lem_add f a (Deep (Four b c d e) m sf) = 
    (f a + f b + size (nodeS f) (Node3 c d e <| m) + digitS f sf) ? (lem_add (nodeS f) (Node3 c d e) m) ===
    (f a + f b + size (nodeS f) m + nodeS f (Node3 c d e) + digitS f sf)  *** QED
lem_add f a (Deep l m sf) = consDigit a l *** QED


{-@ ft1 :: FT Int 10 @-}
ft1 :: FingerTree Int
ft1 = fromList [1,2,3,4,5,6,7,8,9,10]


main :: IO ()
main = do
    print "test"
    print $ fingerTreeSize ft1 -- 10