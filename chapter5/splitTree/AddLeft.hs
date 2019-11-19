{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt"         @-}
{-@ LIQUID "--prune-unsorted"         @-}

module AddLeft where

import SplitDigit
import SplitTreeCore
-- import Liquid.Haskell.ProofCombinators
import Proof

{-@ infix : @-}

{-@ 
addLeftMeasureLemma :: 
    ap:(v -> v -> v) 
    -> e:v
    -> assoc: (x:v -> y:v -> z:v -> {ap x (ap y z) = ap (ap x y) z})
    -> identity : (x:v-> {ap x e = x && ap e x = x})
    -> mes:(a -> v) 
    -> aVal:a
    -> ft:FingerTree v a
    -> { measureFT ap e mes (addLeft ap e mes aVal ft) == ap (mes aVal) (measureFT ap e mes ft) }
@-}
addLeftMeasureLemma :: 
       (v -> v -> v)  -> v -> (v -> v -> v -> Proof) -> (v -> Proof) -> (a -> v)  -> a -> FingerTree v a -> Proof
addLeftMeasureLemma ap e assoc identity mes a Empty
        =   measureFT ap e mes (addLeft ap e mes a Empty) 
        === measureFT ap e mes (Single a) 
        === mes a ? identity (mes a)
        === ap (mes a) e 
        === ap (mes a) (measureFT ap e mes Empty) 
        *** QED
addLeftMeasureLemma ap e assoc identity mes a (Single x)
    =   measureFT ap e mes (addLeft ap e mes a (Single x)) 
    === measureFT ap e mes (deep ap e mes [a] Empty [x]) 
    === measureFT ap e mes (Deep (measureList ap e mes [a] `ap ` measureFT ap e (measureNode ap e mes) Empty `ap` measureList ap e mes [x]) [a] Empty [x]) 
    === measureList ap e mes [a] `ap ` measureFT ap e mes Empty `ap` measureList ap e mes [x] 
    === measureList ap e mes [a] `ap ` e `ap` measureList ap e mes [x]
            ? measureSingletonLemma ap e assoc identity mes a &&& measureSingletonLemma ap e assoc identity mes x    
    === mes a `ap ` e `ap` mes x ? identity (mes a) 
    === mes a `ap ` mes x 
    === ap (mes a) (mes x) 
    === ap (mes a) (measureFT ap e mes (Single x)) 
    *** QED 
addLeftMeasureLemma ap e assoc identity mes aVal ft@(Deep v [b,c,d,e'] m sf)
    -- = un
    =   measureFT ap e mes (addLeft ap e mes aVal (Deep v [b,c,d,e'] m sf))
    === measureFT ap e mes (deep ap e mes [aVal,b] recMid sf)
    -- ? addLeftMeasureLemma ap e assoc identity mes aVal (node3 ap e mes c d e') sf
    === measureFT ap e mes (Deep (ml `ap` mm `ap` mr) [aVal,b] recMid sf)
    === ml `ap` mm `ap` mr
    === mesDig [aVal,b] `ap` mm `ap` mr
    === ap (mes aVal) (mesDig [b]) `ap` mm `ap` mr ? measureSingletonLemma ap e assoc identity mes b
    === ap (mes aVal) (mes b) `ap` mm `ap` mr
    === (ma `ap` mes b) `ap` mm `ap` mr ? addLeftMeasureLemma ap e assoc identity (measureNode ap e mes) (node3 ap e mes c d e') m
    === (ma `ap` mes b) `ap` recs `ap` mr
    === (ma `ap` mes b) `ap` recs' `ap` mr
    === (ma `ap` mes b) `ap` recs2 `ap` mr
    === (ma `ap` mes b) `ap` ap (mes c `ap` mes d `ap` mes e') mtm `ap`  mr ? measureSingletonLemma ap e assoc identity mes e'
    === (ma `ap` mes b) `ap` ap (mes c `ap` mes d `ap` mesDig [e']) mtm `ap`  mr
    === (ma `ap` mes b) `ap` ap ((mes c `ap` mes d) `ap` mesDig [e']) mtm `ap` mr ? assoc (mes c) (mes d) (mesDig [e'])
    === (ma `ap` mes b) `ap` ap (mes c `ap` (mes d `ap` mesDig [e'])) mtm `ap`  mr
    === (ma `ap` mes b) `ap` ap (mes c `ap` mesDig [d,e']) mtm `ap`  mr
    === (ma `ap` mes b) `ap` ap (mesDig [c,d,e']) mtm `ap`  mr
    === (ap ma (mes b)) `ap` ap (mesDig [c,d,e']) mtm `ap`  mr
    === ap (ap ma (mes b)) (ap (mesDig [c,d,e']) mtm `ap`  mr)
    -- === ap ma (mes b `ap` mes c `ap` mes d `ap` mes e') mtm `ap`  mr ? measure4Lemma ap e assoc identity mes b c d e'
    === ap (ap ma (mes b)) (mesDig [c,d,e']) `ap` mtm `ap` mtr ? assoc ma (mes b) (mesDig [c,d,e'])
    === ap ma (ap (mes b) (mesDig [c,d,e'])) `ap` mtm `ap` mtr
    === ap ma (mesDig [b,c,d,e']) `ap` mtm `ap` mtr
    === ap ma mtl `ap` mtm `ap` mtr
    === (ap ma mtl) `ap` mtm `ap` mtr
    === (ap (ap ma mtl) mtm) `ap` mtr ? assoc ma mtl mtm
    === ap ma (ap mtl mtm) `ap` mtr
    === ap (ap ma (ap mtl mtm)) mtr ? assoc ma (ap mtl mtm) mtr
    === ap ma (ap (ap mtl mtm) mtr)
    === ap ma (mtl `ap` mtm `ap` mtr) ? ftMonoidAxiom ap e mes v [b,c,d,e'] m sf
    === ap ma v 
    === ap ma (measureFT ap e mes ft)
    *** QED
    where
        mtl = measureList ap e mes [b,c,d,e']
        mtm = measureFT ap e (measureNode ap e mes) m
        mtr = measureList ap e mes sf
        ma = mes aVal
        recMid = addLeft ap e (measureNode ap e mes) (node3 ap e mes c d e') m
        ml = measureList ap e mes [aVal,b]
        mesDig = measureList ap e mes
        mm = measureFT ap e  (measureNode ap e mes) recMid
        
        mr = measureList ap e mes sf
        recs = ap (measureNode ap e mes (node3 ap e mes c d e')) (measureFT ap e (measureNode ap e mes) m)
        recs' = ap (measureNode ap e mes (Node3 (mes c `ap` mes d `ap` mes e') c d e')) (measureFT ap e (measureNode ap e mes) m)
        recs2 = ap (mes c `ap` mes d `ap` mes e') (measureFT ap e (measureNode ap e mes) m)

addLeftMeasureLemma ap e assoc identity mes a ft@(Deep v l m r)
    =   measureFT ap e mes (addLeft ap e mes a (Deep v l m r))
    === measureFT ap e mes (deep ap e mes (a:l) m r) 
    === measureFT ap e mes (Deep (measureList ap e mes (a:l) `ap ` mm `ap` mr) (a:l) m r) 
    === measureList ap e mes (a:l) `ap ` mm `ap` mr
    === ap (mes a) ml  `ap` mm `ap` mr 
    === (ap (mes a) ml  `ap` mm) `ap` mr 
    === ap (ap ma ml) mm `ap` mr 
    === ap (ap (ap ma ml) mm) mr ? assoc ma ml mm
    === ap (ap ma (ap ml mm)) mr ? assoc ma (ap ml mm) mr
    === ap ma (ap (ap ml mm) mr)
    === ap (mes a) (ml `ap` mm `ap` mr)
            ? ftMonoidAxiom ap e mes v l m r
    === ap (mes a) v ? ftMonoidAxiom ap e mes v l m r
    === ap (mes a) (measureFT ap e mes ft)
    *** QED
    where
        ma = mes a
        ml = measureList ap e mes l
        mm = measureFT ap e (measureNode ap e mes) m
        mr = measureList ap e mes r
    
-- {-@ measure isDeep :: FingerTree v a -> Bool @-}
-- isDeep Empty = False
-- isDeep Single{} = False
-- isDeep Deep{} = True

{-@ reflect getV @-}
{-@ getV :: {ft:FingerTree v a | True} -> v @-}
getV (Deep v _ _ _ ) = v 
getV _ = un 

{-@ 
ftMonoidAxiom :: 
    ap:(v -> v -> v) 
    -> e:v
    -> mes:(a -> v)
    -> v:v
    -> l:Dig a
    -> m:FingerTree v (Node v a)
    -> r:Dig a
    ->
    { 
        measureFT ap e mes (Deep v l m r) == v && 
            ap (ap (measureList ap e mes l) (measureFT ap e (measureNode ap e mes) m)) (measureList ap e mes r) == v
    }
@-}
ftMonoidAxiom :: 
        (v -> v -> v) 
    -> v
    -> (a -> v) 
    -> v
    -> Digit a
    -> FingerTree v (Node v a)
    -> Digit a
    -> Proof
ftMonoidAxiom ap e mes v l m r = un

{-@ measureSingletonLemma :: 
    ap:(v -> v -> v) 
    -> e:v
    -> assoc: (x:v -> y:v -> z:v -> {ap x (ap y z) = ap (ap x y) z})
    -> identity : (x:v-> {ap x e = x && ap e x = x})
    -> mes:(a -> v) 
    -> x:a 
    -> { measureList ap e mes [x] == mes x}
@-}
measureSingletonLemma ::    (v -> v -> v) 
    -> v
    -> (v -> v -> v -> Proof)
    -> (v -> Proof)
    -> (a -> v) 
    -> a
    -> Proof
measureSingletonLemma ap e assoc identity mes x
    =   measureList ap e mes [x] 
    === ap (mes x) (measureList ap e mes []) 
    === ap (mes x) e ? identity (mes x) 
    === mes x
    *** QED 




main = undefined