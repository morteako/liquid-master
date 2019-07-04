{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--no-adt"         @-}
{-@ LIQUID "--max-case-expand=6"         @-}
{-@ LIQUID "--ple"            @-}

module FTapp where

import Proof
import FT

{-@ infix +++ @-}

{-@ reflect ftSize @-}
{-@ ftSize :: FingerTree a -> Nat@-}
ftSize :: FingerTree a -> Int
ftSize Empty = 0
ftSize (Single _) = 1
ftSize (Deep l xs r) = diglen l + ftSize xs + diglen r

{-@ reflect diglen @-}
{-@ diglen :: [a] -> Nat @-}
diglen :: [a] -> Int
diglen []       = 0
diglen (x:xs)   = 1 + diglen xs


{-@ infix : @-}
{-@ diglen_lem :: v:a -> d:[a] -> {1 + diglen d == diglen (v:d)} @-}
diglen_lem :: a -> Digit a -> Proof
diglen_lem a xs = trivial

-- {-@ lazy app3 @-}
-- {-@ reflect app3 @-}
-- {-@ app3 :: fa:FingerTree a -> ts:[a] -> fb:FingerTree a -> ft:FingerTree a  @-}
-- app3 :: FingerTree a -> [a] -> FingerTree a -> FingerTree a
-- app3 Empty [] xs = xs
-- app3 Empty (t:ts) xs = t <| app3 Empty ts xs
-- app3 xs [] Empty = xs
-- app3 xs (t:ts) Empty = app3 xs ts Empty |> t
-- app3 (Single x) ts ys = x <| app3 Empty ts ys
-- app3 xs ts (Single y) = app3 xs ts Empty |> y
-- -- app3 (Deep pr1 m1 sf1) ts (Deep pr2 m2 sf2) = Deep pr1 (app3 m1 (nodes (sf1 +++ ts +++ pr2)) m2) sf2
-- app3 _ _ _ = un


--CANT PROVE TERMINATION!?
-- {-@ app3t :: fa:FingerTree a -> ts:[a] -> fb:FingerTree a -> (l:_,m:_,r:_) /  @-}
-- app3t :: FingerTree a -> [a] -> FingerTree a -> FingerTree a
-- app3t Empty [] xs = xs
-- app3t Empty (t:ts) xs = t <| app3t Empty ts xs ? un
-- app3t xs [] Empty = xs
-- app3t xs (t:ts) Empty = app3t xs ts Empty |> t ? un
-- app3t (Single x) ts ys = (x <| app3t Empty ts ys) ? un


--Safe, but takes a lot of time and CPU to verify, so commented out
-- {-@ app3t :: fa:FingerTree a -> ts:[a] -> fb:FingerTree a -> {v:Int | v < ftSize fa + diglen ts + ftSize fb}  @-}
-- app3t :: FingerTree a -> [a] -> FingerTree a -> Int
-- app3t Empty [] xs = 0
-- app3t Empty (t:ts) xs = ftSize Empty + diglen ts + ftSize xs 
-- app3t xs [] Empty = 0
-- app3t xs (t:ts) Empty = ftSize xs + diglen ts + ftSize Empty
-- app3t (Single x) ts ys = ftSize Empty + diglen ts + ftSize ys
-- app3t xs ts (Single y) = ftSize xs + diglen ts + ftSize Empty
-- app3t ft1@(Deep pr1 m1 sf1) ts ft2@(Deep pr2 m2 sf2) = ftSize m1 + diglen (nodes (sf1 +++ ts +++ pr2)) + ftSize m2
--     ?   (ftSize ft1 + diglen ts + ftSize ft2
--     === diglen pr1 + ftSize m1 + diglen sf1 + diglen ts + diglen pr2 + ftSize m2 + diglen sf2
--     === ftSize m1 + ftSize m2 + diglen pr1 + diglen sf1 + diglen ts + diglen pr2 + diglen sf2
--     === ftSize m1 + ftSize m2 + diglen (pr1 +++ sf1 +++ ts +++ pr2 +++ sf2)
--     === ftSize m1 + ftSize m2 + diglen (pr1 +++ (sf1 +++ ts +++ pr2 +++ sf2))
--     === ftSize m1 + ftSize m2 + diglen (pr1 +++ (sf1 +++ ts +++ pr2 +++ sf2))
--         ? nodes_lem pr1 (sf1 +++ ts +++ pr2 +++ sf2)
--     =>= ftSize m1 + ftSize m2 + diglen (sf1 +++ ts +++ pr2 +++ sf2) 
--     === ftSize m1 + ftSize m2 + diglen (sf1 +++ (ts +++ (pr2 +++ sf2))) 
--     === ftSize m1 + ftSize m2 + diglen (sf1 +++ (ts +++ (pr2 +++ sf2))) 
--         ? list_assoc sf1 ts (pr2 +++ sf2)
--     === ftSize m1 + ftSize m2 + diglen ((sf1 +++ ts) +++ (pr2 +++ sf2))
--         ? list_assoc (sf1+++ts) pr2 sf2
--     === ftSize m1 + ftSize m2 + diglen (((sf1 +++ ts) +++ pr2) +++ sf2)
--         ? diglen_comm ((sf1 +++ ts) +++ pr2) sf2
--     =>= ftSize m1 + ftSize m2 + diglen (nodes (sf1 +++ ts +++ pr2))
--     *** QED)


{-@ nodes_lem :: xs:[a] -> ys:[a] -> { diglen (xs +++ ys) >= diglen ys} @-}
nodes_lem :: [a] -> [a] -> Proof
nodes_lem [] ys = trivial
nodes_lem (x:xs) ys
    =   diglen ((x:xs) +++ ys)
    === diglen (x:(xs +++ ys))
    === 1 + diglen (xs +++ ys)
    =>= diglen (xs +++ ys) ? nodes_lem xs ys
    =>= diglen ys
    *** QED

{-@ diglen_comm :: xs:[a] -> ys:[a] -> { diglen (xs +++ ys) == diglen (ys +++ xs)} @-}
diglen_comm :: [a] -> [a] -> Proof
diglen_comm xs ys = un

{-@ lem1 :: x:a -> d:Dig a -> ft:FingerTree a -> 
    { ftSize (Single x) + diglen d + ftSize ft == 1 + ftSize Empty + diglen d + ftSize ft} @-}
lem1 :: a -> Digit a -> FingerTree a -> Proof
lem1 a d ft = trivial

{-@ 
right_id :: 
        x:[a]
    ->  { x +++ [] == x } 
@-}
right_id :: [a] ->  Proof
right_id [] = trivial
right_id (x:xs) = right_id xs


{-@ 
list_assoc :: 
        x:[a]
    ->  y:[a]
    ->  z:[a]
    ->  { x +++ (y +++ z) == (x +++ y) +++ z } 
@-}
list_assoc :: [a] -> [a] -> [a] -> Proof
list_assoc [] y z
    =   [] +++ (y +++ z)
    === (y +++ z)
    === ([] +++ y) +++ z
    *** QED
list_assoc (x:xs) y z
    =   (x:xs) +++ (y +++ z)
    === x:(xs +++ (y +++ z)) ? list_assoc xs y z
    === x:((xs +++ y) +++ z) 
    === ((x:xs) +++ y) +++ z
    *** QED 


-- {-@ reflect app @-}
-- {-@ app :: FingerTree a -> FingerTree a -> FingerTree a @-}
-- app :: FingerTree a -> FingerTree a -> FingerTree a
-- app xs ys = app3 xs [] ys


-- {-@ 
-- app_proof :: 
--       ft1 : _
--   ->  ft2 : _
--   ->  {fingerTreeSize ft1 + fingerTreeSize ft2 == fingerTreeSize (app ft1 ft2)} 
-- @-}
-- app_proof :: FingerTree a -> FingerTree a -> Proof
-- -- app_proof Empty ys = trivial
-- -- app_proof xs Empty = trivial
-- app_proof xs ys = un

-- infixl 5 +++
{-@ reflect +++ @-}
{-@ +++ :: xs:[a] -> ys:[a] -> {zs:[a] | len xs + len ys == len zs && diglen xs + diglen ys == diglen zs}  @-}
(+++) :: [a] -> [a] -> [a]
[] +++ ys = ys
(x:xs) +++ ys = x: (xs +++ ys)

{-@ reflect nodes @-}
{-@ nodes :: {xs:[a]| len xs >= 2} -> {ns:[Node a] | len ns >= 1 && diglen ns < diglen xs}  @-}
nodes :: [a] -> [Node a]
nodes [a,b] = [Node2 a b]
nodes [a,b,c] = [Node3 a b c]
nodes [a,b,c,d] = [Node2 a b,Node2 c d]
nodes (a:b:c:xs) = Node3 a b c : nodes xs

