{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-adt"         @-}
{-@ LIQUID "--prune-unsorted"         @-}

module SplitTreeProofs where

-- import Liquid.Haskell.ProofCombinators
import Proof
import SplitDigit
import AddLeft hiding (main)
import SplitTreeCore hiding (main)



{-@ infix : @-}
--------------------------------------------------------------------------
--Proofs

{-@ 
splitTree_notP :: 
        ap:(v -> v -> v)
    ->  e:v
    -> assoc: (x:v -> y:v -> z:v -> {ap x (ap y z) = ap (ap x y) z})
    -> identity : (x:v-> {ap x e = x && ap e x = x})
    ->  mes:(a -> v) 
    ->  p:(v -> Bool) 
    ->  i:v
    ->  ft:NFT v a
    -> prnp:{ Proof | not (p i) } 
    -> prp:{ Proof | p (ap i (measureFT ap e mes ft)) } 
    ->  { 
            not (p (ap i (measureFT ap e mes (getLFT (splitTree ap e mes p i ft)))))
        }
@-}
splitTree_notP :: (v -> v -> v) -> v -> (v -> v -> v -> Proof) -> (v -> Proof) -> (a -> v) -> (v-> Bool) -> v -> FingerTree v a -> Proof -> Proof -> Proof
splitTree_notP ap e assoc identity mes p i (Single s) prnp prp
    =
            not (p (ap i (measureFT ap e mes (getLFT (splitTree ap e mes p i (Single s))))))
        === not (p (ap i (measureFT ap e mes (getLFT (FSplit Empty s Empty)))))
        === not (p (ap i (measureFT ap e mes Empty)))
        === not (p (ap i e)) ? identity i
        === not (p i)
        *** QED
splitTree_notP ap e assoc identity mes p i (Deep v pr Empty sf) prnp prp 
    = un
splitTree_notP ap e assoc identity mes p i ft@(Deep v pr m sf) prnp prp 
    |   p vpr = 
                let recur = 
                        let 
                            ds@(DSplit l x r) = splitDigitProved ap e assoc identity mes p i pr prnp prp
                            res = FSplit (toTree ap e mes l) x (deepL ap e mes r m sf 1)
                            lemma = 
                                not (p (ap i (measureFT ap e mes (getLFT res))))
                                === not (p (ap i (measureFT ap e mes (toTree ap e mes (getL ds)))))
                                === not (p (ap i (measureFT ap e mes (toTree ap e mes l)))) ? toTreePreservesMonoid ap e assoc identity mes l
                                === not (p (ap i (measureDigit0 ap e mes l)))
                                *** QED

                        in  
                            res ? lemma 
                in
                    toProof $ recur ? 
                        (getLFT (splitTree ap e mes p i ft)
                        === getLFT recur
                        *** QED)   
    |   p vm = un
    |   not (p vpr) && not (p vm) =
            let 
                mesDig = measureDigit0 ap e mes
                mesFTN = measureFT ap e (measureNode ap e mes)
                mesFT = measureFT ap e mes
                recur = 
                    let 
                        prpvm
                            = p (ap i (mesFT ft))
                            === p (ap i (mesFT (Deep v pr m sf))) ? ftMonoidAxiom ap e mes v pr m sf 
                            === p (ap i v) ? ftMonoidAxiom ap e mes v pr m sf 
                            === p (ap i (ap (ap (mesDig pr) (mesFTN m)) (mesDig sf)))
                                    ? assoc i (ap (mesDig pr) (mesFTN m)) (mesDig sf)
                            === p (ap (ap i (ap (mesDig pr) (mesFTN m))) (mesDig sf))
                                    ? assoc i (mesDig pr) (mesFTN m)
                            === p (ap (ap (ap i (mesDig pr)) (mesFTN m)) (mesDig sf))
                            *** QED

                        ds@(DSplit l x r) = splitDigitProved ap e assoc identity mes p vm sf (not (p vm) *** QED) prpvm
                        res =  FSplit (deepR ap e mes pr m l 1) x (toTree ap e mes r)
                          
                        lemma
                            =   not (p (vm `ap` mesDig l)) ? (toProof ds &&& toProof l)
                            === not (p (ap (vpr `ap` mesFTN m) (mesDig l)))
                            === not (p (ap (ap vpr  (mesFTN m)) (mesDig l)))
                            === not (p (ap (ap (ap i (mesDig pr)) (mesFTN m)) (mesDig l)))
                                ? assoc i (mesDig pr) (mesFTN m)
                            === not (p (ap (ap i (ap (mesDig pr) (mesFTN m))) (mesDig l)))
                                    ? assoc i (ap (mesDig pr) (mesFTN m)) (mesDig l)
                            === not (p (ap i (ap (ap (mesDig pr) (mesFTN m)) (mesDig l))))
                                    ? assoc (mesDig pr) (mesFTN m) (mesDig l)
                            === not (p (ap i (ap (mesDig pr) (ap (mesFTN m) (mesDig l)))))
                                    ? deepRPreservesMonoid ap e assoc identity mes pr m l
                            === not (p (ap i 
                                        (mesFT (deepR ap e mes pr m l 1))) )
                            === not (p (ap i (mesFT (deepR ap e mes pr m l 1))))
                            === not (p (ap i (mesFT (getLFT res))))
                            *** QED
                      

                    in  
                        res ? lemma &&& toProof ds &&& toProof l
            in
            
                toProof $ recur ? 
                    (getLFT (splitTree ap e mes p i ft)
                    === getLFT recur
                    *** QED) 
        
    where 
        vpr = ap i (measureDigit0 ap e mes pr) 
        vm = vpr `ap` measureFT ap e (measureNode ap e mes) m
   


{-@ deepRPreservesMonoid :: 
       ap:(v -> v -> v) 
    -> e:v
    -> assoc: (x:v -> y:v -> z:v -> {ap x (ap y z) = ap (ap x y) z})
    -> identity : (x:v-> {ap x e = x && ap e x = x})
    -> mes:(a -> v) 
    -> pr:[a] 
    -> m:FingerTree v (Node v a) 
    -> sf:[a] 
    ->
    { 
        measureFT ap e mes (deepR ap e mes pr m sf 1) == 
            ap  (measureDigit0 ap e mes pr) 
                (ap (measureFT ap e (measureNode ap e mes) m)
                    (measureDigit0 ap e mes sf))
    }
 @-}
deepRPreservesMonoid :: (v -> v -> v) -> v -> (v -> v -> v -> Proof) -> (v -> Proof) -> (a -> v) -> [a] -> FingerTree v (Node v a) -> [a] -> Proof
deepRPreservesMonoid = un

{-@ toTreePreservesMonoid :: 
       ap:(v -> v -> v) 
    -> e:v
    -> assoc: (x:v -> y:v -> z:v -> {ap x (ap y z) = ap (ap x y) z})
    -> identity : (x:v-> {ap x e = x && ap e x = x})
    -> mes:(a -> v) 
    -> l:[a] 
    -> { measureFT ap e mes (toTree ap e mes l) == measureDigit0 ap e mes l }
@-}
toTreePreservesMonoid :: (v -> v -> v) -> v -> (v -> v -> v -> Proof) -> (v -> Proof) -> (a -> v) -> [a] -> Proof
toTreePreservesMonoid ap e assoc identity mes []
    =   measureFT ap e mes (toTree ap e mes [])
    === measureFT ap e mes Empty
    === e
    === measureDigit0 ap e mes []
    *** QED
toTreePreservesMonoid ap e assoc identity mes [a]
    =   measureFT ap e mes (toTree ap e mes [a])
    === measureFT ap e mes (Single a)
    === mes a ? measureSingletonLemma ap e assoc identity mes a
    === measureDigit0 ap e mes [a]
    *** QED
toTreePreservesMonoid ap e assoc identity mes (a:as)
    =   measureFT ap e mes (toTree ap e mes (a:as))
    === measureFT ap e mes (addLeft ap e mes a (toTree ap e mes as)) ? addLeftMeasureLemma ap e assoc identity mes a  (toTree ap e mes as)
    === ap (mes a) (measureFT ap e mes (toTree ap e mes as)) ? toTreePreservesMonoid ap e assoc identity mes as
    === ap (mes a) (measureDigit0 ap e mes as)
    === measureDigit0 ap e mes (a:as)
    *** QED





main = undefined