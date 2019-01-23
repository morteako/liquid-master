{-@ LIQUID "--total" @-}
{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--no-adt"         @-}   -- Tells LH to NOT embed `FingerTree` natively to SMT (since SMT can't handle polymorphic recursion)
{-@ LIQUID "--ple"            @-}   -- Enables "logical evaluation", a method for "type-level computation" with the reflected functions


import Liquid.Haskell.ProofCombinators --local


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

-- {-@ lazy un @-}
-- un = un

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




{-@ lem_add_to1 ::  x:a -> t:FingerTree a -> { size to1 (x <| t) == size to1 t + to1 x }  @-}
lem_add_to1 :: a -> FingerTree a -> Proof
lem_add_to1 a t = lem_add t to1 a

{-@ lem_add :: t:FingerTree a -> f:(a -> Int) -> x:a -> { size f (x <| t) == size f t + f x }  @-}
lem_add :: FingerTree a -> (a -> Int) -> a ->  Proof
lem_add Empty f a  = trivial
lem_add (Single _) f a  = trivial
lem_add (Deep (Four b c d e) m sf) f a  = 
    (f a + f b + size (nodeS f) (Node3 c d e <| m) + digitS f sf) ===
    (f a + f b + size (nodeS f) (Node3 c d e <| m) + digitS f sf) ? (lem_add m (nodeS f) (Node3 c d e)) ===
    (f a + f b + size (nodeS f) m + nodeS f (Node3 c d e) + digitS f sf) *** QED
lem_add  (Deep l m sf) f a = consDigit a l *** QED


(|>) ::FingerTree a -> a -> FingerTree a
Empty |> a              =  Single a
Single a |> b           =  Deep (One a) Empty (One b)
Deep pr m (Four a b c d) |> e = 
    Deep pr (m |> Node3 a b c) (Two d e)
Deep pr m sf |> x     =
    Deep pr m (snocDigit sf x)
{-@ reflect |> @-}
{-@ infix |> @-}

{-@ reflect consDigit @-}
{-@ consDigit :: v:a -> {d:Digit a | digitSize d < 4} -> {dd : Digit a | digitSize dd == digitSize d + 1} @-}
consDigit :: a -> Digit a -> Digit a
consDigit a (One b) = Two a b
consDigit a (Two b c) = Three a b c
consDigit a (Three b c d) = Four a b c d

{-@ reflect snocDigit @-}
{-@ snocDigit :: {d:Digit a | digitSize d < 4} -> v:a -> {dd : Digit a | digitSize dd == digitSize d + 1} @-}
snocDigit :: Digit a -> a -> Digit a
snocDigit (One a) b = Two a b
snocDigit (Two a b) c = Three a b c
snocDigit (Three a b c) d = Four a b c d

{-@ lem_add_r_to1 ::  x:a -> t:FingerTree a -> { size to1 (t |> x) == size to1 t + to1 x }  @-}
lem_add_r_to1 :: a -> FingerTree a -> Proof
lem_add_r_to1 a t = lem_add_r t to1 a

{-@ lem_add_r :: t:FingerTree a -> f:(a -> Int) -> x:a -> { size f (t |> x) == size f t + f x } @-}
lem_add_r :: FingerTree a -> (a -> Int) -> a -> Proof
lem_add_r Empty f a = trivial
lem_add_r (Single _) f a = trivial
lem_add_r (Deep l m (Four a b c d)) f e =
    (f d + f e + size (nodeS f) (m |> Node3 a b c) + digitS f l) ? (lem_add_r m (nodeS f) (Node3 a b c)) ===
    (f d + f e + size (nodeS f) m + nodeS f (Node3 a b c) + digitS f l) *** QED
lem_add_r (Deep l m r) f a = snocDigit r a *** QED
        

{-@ fromListR :: xs:[a] -> {ft : FingerTree a | fingerTreeSize ft == len xs} @-}
fromListR :: [a] -> FingerTree a
fromListR xs = fromR xs ? lem_from_r xs


{-@ reflect fromR @-}
{-@ fromR :: xs:[a] -> FingerTree a @-}
fromR :: [a] -> FingerTree a
fromR []     = Empty
fromR (x:xs) = fromR xs |> x

{-@ lem_from_r :: xs:[a] -> { len xs == fingerTreeSize (fromR xs) } @-}
lem_from_r :: [a]  -> Proof
lem_from_r [] = trivial
lem_from_r (x:xs) = lem_add_r_to1 x (fromR xs) &&& lem_from_r xs

{-@ ft1 :: FT Int 10 @-}
ft1 :: FingerTree Int
ft1 = fromList [1,2,3,4,5,6,7,8,9,10]

{-@ ft2 :: FT Int 10 @-}
ft2 :: FingerTree Int
ft2 = fromListR [1,2,3,4,5,6,7,8,9,10]



main :: IO ()
main = do
    print "test"
    print $ fingerTreeSize ft1 -- 10

