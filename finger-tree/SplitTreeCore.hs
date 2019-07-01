{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt"         @-}

module SplitTreeCore where

import SplitDigit


{-@ data FSplit v a = FSplit {sl::(FingerTree v a), sx::a, sr::(FingerTree v a)}  @-}
data FSplit v a = FSplit (FingerTree v a) a (FingerTree v a) 

data Node v a = Node2 {val::v, a2::a, b2::a} | Node3 {val::v, a3::a, b3::a, c3:: a}
    deriving (Show)

{-@ type Dig a = {v:[a] | len v >= 1 && len v <= 4} @-}
type Digit a = [a]

{-@ data FingerTree v a = 
    Deep {vv::v, lft::(Dig a) , mid::(FingerTree v (Node v a)), rft :: (Dig a)}
    | Single a
    |   Empty
 @-}
data FingerTree v a
    = Empty
    | Single a
    | Deep v (Digit a) (FingerTree v (Node v a)) (Digit a)
    deriving Show


{-@ reflect getLFT @-}
getLFT (FSplit l _ _) = l

{-@ measure nonEmpty @-}
nonEmpty Empty = False
nonEmpty Single{} = True
nonEmpty Deep{} = True

-- views

{-@ measure ftDigsize @-}
{-@ ftDigsize :: FingerTree v a -> {v:Int| v >= 0} @-}
ftDigsize :: FingerTree v a -> Int
ftDigsize Empty = 0
ftDigsize Single{} = 1
ftDigsize (Deep _ [_] m _) = 1 + ftDigsize m
ftDigsize (Deep _ [_,_] m _) = 2 + ftDigsize m
ftDigsize (Deep _ [_,_,_] m _) = 3 + ftDigsize m
ftDigsize (Deep _ [_,_,_,_] m _) = 4 + ftDigsize m


{-@ reflect digitS @-} 
{-@ digitS :: (a -> Int) -> Dig a -> Int @-}
digitS :: (a -> Int) -> Digit a -> Int
digitS f [a]       = f a
digitS f (a:as) = f a + digitS f as

{-@ reflect nodeS @-}
nodeS :: (a -> Int) -> Node v a -> Int
nodeS f (Node2 _ a b)   = f a + f b
nodeS f (Node3 _ a b c) = f a + f b + f c

----------------------------------------------------------------------
--views


data ViewR s a = NilR | ConsR (s a) a

{-@ reflect viewR @-}
{-@ viewR :: (v -> v -> v) -> v ->  (a -> v) -> ft:FingerTree v a -> ViewR (FingerTree v) a / [ftDigsize ft, 0]@-}
viewR :: (v -> v -> v) -> v ->  (a -> v) -> FingerTree v a -> ViewR (FingerTree v) a
viewR ap e mes Empty                = NilR
viewR ap e mes (Single x)           = ConsR Empty x
viewR ap e mes (Deep v pr m (s:sf)) = ConsR (deepR ap e mes pr m sf) s



{-@ reflect deepR @-}
{-@ 
deepR ::  (v -> v -> v) -> v ->  (a -> v) -> Dig a -> m:FingerTree v (Node v a) -> {v:[a] | len v <= 4 } -> FingerTree v a / [ftDigsize m, 1]
@-}
deepR ::  (v -> v -> v) -> v ->  (a -> v) -> Digit a -> FingerTree v (Node v a) -> [a] -> FingerTree v a
deepR ap e mes pr m [] = case viewR ap e (measureNode ap e mes) m of
    NilR -> toTree ap e mes pr
    ConsR m' a -> deep ap e mes pr m' (nodeToList a)
deepR ap e mes pr m (s:sf) = deep ap e mes pr m (s:sf)

data ViewL s a = NilL | ConsL a (s a)


{-@ reflect viewL @-}
{-@ viewL :: (v -> v -> v) -> v ->  (a -> v) -> ft:FingerTree v a -> ViewL (FingerTree v) a / [ftDigsize ft, 0]@-}
viewL :: (v -> v -> v) -> v ->  (a -> v) -> FingerTree v a -> ViewL (FingerTree v) a
viewL ap e mes Empty                = NilL
viewL ap e mes (Single x)           = ConsL x Empty
viewL ap e mes (Deep v (p:pr) m sf) = ConsL p (deepL ap e mes pr m sf) 



{-@ reflect deepL @-}
{-@ 
deepL ::  (v -> v -> v) -> v ->  (a -> v) -> {v:[a] | len v <= 4 } -> m:FingerTree v (Node v a) -> Dig a -> FingerTree v a / [ftDigsize m, 1]
@-}
deepL ::  (v -> v -> v) -> v ->  (a -> v) -> [a] -> FingerTree v (Node v a) -> Digit a -> FingerTree v a
deepL ap e mes [] m sf = case viewL ap e (measureNode ap e mes) m of
    NilL -> toTree ap e mes sf
    ConsL a m' -> deep ap e mes (nodeToList a) m' sf
deepL ap e mes (p:pr) m sf = deep ap e mes (p:pr) m sf


{-@ type NFT v a = {ft : FingerTree v a | nonEmpty ft} @-}

{-@ reflect toTree @-}
{-@ 
toTree ::
        (v -> v -> v) 
    -> v 
    -> (a -> v)
    -> [a]
    -> FingerTree v a 
@-}
-- -> {vv:[a] | len vv <= 4}      NOT SURE
toTree ap e mes [] = Empty --NOT SURE
toTree ap e mes [a] = Single a
toTree ap e mes (a:as) = addLeft ap e mes a (toTree ap e mes as)


{-@ reflect addLeft @-}
addLeft :: (v -> v -> v) -> v ->  (a -> v) -> a -> FingerTree v a -> FingerTree v a
addLeft ap eEle mes a (Empty)                      = Single a
addLeft ap eEle mes a (Single b)                   = deep ap eEle mes [a] Empty [b]
addLeft ap eEle mes a (Deep _ [b,c,d,e] m sf)      = deep ap eEle mes [a,b] (addLeft ap eEle (measureNode ap eEle mes) (node3 ap eEle mes c d e) m) sf
addLeft ap eEle mes a (Deep _ l m r)               = deep ap eEle mes (a:l) m r 



-- The nonEmpty-case is hard, because can't use proofs inside a function that is going to be reflected
{-@ reflect splitTree @-}
{-@ 
splitTree :: 
        ap:(v -> v -> v)
    ->  e:v
    ->  mes:(a -> v) 
    ->  p:(v -> Bool) 
    ->  i:v
    ->  ft:NFT v a
    ->  FSplit v a
@-}
splitTree :: (v -> v -> v) -> v -> (a -> v) -> (v-> Bool) -> v -> FingerTree v a -> FSplit v a 
splitTree ap e mes p i (Single x) = FSplit Empty x Empty
splitTree ap e mes p i (Deep v pr Empty sf )
    | p vpr = 
        let 
            DSplit l x r = splitDigitMon ap mes p i pr
        in  FSplit (toTree ap e mes l) x (deepL ap e mes r Empty sf)
    | otherwise = 
        let DSplit l x r = splitDigitMon ap mes p vpr sf
        in  FSplit (deepR ap e mes pr Empty l) x (toTree ap e mes r)
    where 
        vpr = i `ap` measureDigit0 ap e mes pr
splitTree ap e mes p i (Deep v pr m sf )
    | p vpr = 
        let 
            DSplit l x r = splitDigitMon ap mes p i pr
        in  FSplit (toTree ap e mes l) x (deepL ap e mes r m sf)
    | p vm = 
        let 
            FSplit ml xs mr = splitTree ap e (measureNode ap e mes) p vpr m
            DSplit l x r = splitDigitMon ap mes p (vpr `ap` measureFT ap e (measureNode ap e mes) ml) (nodeToList xs)
        in 
            FSplit (deepR ap e mes pr ml l) x (deepL ap e mes r mr sf)
    | otherwise = 
        let DSplit l x r = splitDigitMon ap mes p vm sf
        in  FSplit (deepR ap e mes pr m l) x (toTree ap e mes r)     
    where 
        vpr = i `ap` measureDigit0 ap e mes pr
        vm = vpr `ap` measureFT ap e (measureNode ap e mes) m


---------------------------------------------------------------
-- Measure functions
{-@ reflect measureFT @-}
{-@ 
measureFT :: 
        ap:(v -> v -> v)
    ->  e : v
    ->  mes:(a -> v) 
    ->  d:FingerTree v a
    ->  v 
@-}
measureFT :: (v -> v -> v) -> v ->  (a -> v) -> FingerTree v a -> v
measureFT ap e mes Empty = e
measureFT ap e mes (Single x) = mes x
measureFT ap e mes (Deep v _ _ _) = v

{-@ reflect measureNode @-}
{-@ 
measureNode :: 
        ap:(v -> v -> v)
    ->  e : v
    ->  mes:(a -> v) 
    ->  d:Node v a
    ->  v 
@-}
measureNode :: (v -> v -> v) -> v ->  (a -> v) -> Node v a -> v
measureNode ap e mes (Node2 v _ _) = v
measureNode ap e mes (Node3 v _ _ _) = v


---------------------------------------------------------------
-- smart constructors
{-@ reflect node2 @-}
{-@ 
node2 :: 
        ap:(v -> v -> v)
    ->  e : v
    ->  mes:(a -> v) 
    ->  a
    ->  a
    ->  Node v a 
@-}
node2 :: (v -> v -> v) -> v ->  (a -> v) -> a -> a -> Node v a
node2 ap e mes a b = Node2 (mes a `ap` mes b) a b

{-@ reflect node3 @-}
{-@ 
node3 :: 
        ap:(v -> v -> v)
    ->  e : v
    ->  mes:(a -> v) 
    ->  a
    ->  a
    ->  a
    ->  Node v a 
@-}
node3 :: (v -> v -> v) -> v ->  (a -> v) -> a -> a -> a -> Node v a
node3 ap e mes a b c = Node3 (mes a `ap` mes b `ap` mes c) a b c

{-@ reflect nodeToList @-}
{-@ nodeToList :: Node v a -> {d:[a] | len d == 2 || len d == 3} @-}
nodeToList (Node2 _ a b) = [a,b]
nodeToList (Node3 _ a b c) = [a,b,c]


{-@ reflect deep @-}
{-@ 
deep :: 
        (v -> v -> v) 
    ->  v 
    ->  (a -> v) 
    ->  Dig a 
    ->  FingerTree v (Node v a) 
    ->  Dig a
    ->  FingerTree v a 
@-}
deep :: 
    (v -> v -> v) -> v ->  (a -> v) -> [a] -> FingerTree v (Node v a) -> [a] -> FingerTree v a
deep ap e mes pr m sf = 
    Deep 
        (measureDigit0 ap e mes pr `ap` measureFT ap e (measureNode ap e mes) m `ap` measureDigit0 ap e mes sf)
        pr 
        m 
        sf

main = do
    print 1