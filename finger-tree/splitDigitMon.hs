{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--total" @-}


module SplitDigit 
(
    un,
    cons,
    (++),
    app_lemma_help2,
    append_assoc,
    append_id_right,
    splitDigit,
    Split
) where

import Prelude hiding ((++))
import Proof


{-@ reflect un @-}
un :: a
un = un

--Because of errors using (:) in refinements
{-@ reflect cons @-}
{-@ cons :: x:a -> xs:[a] -> xxs:[a] @-}
cons x xs = x:xs

{-@ infix ++ @-}
{-@ reflect ++ @-}
(++) :: [a] -> [a] -> [a]
[] ++ ys = ys
(x:xs) ++ ys = x:xs ++ ys

{-@ append_id_right :: xs:[a] -> { xs ++ [] == xs} @-}
append_id_right [] = trivial
append_id_right (x:xs)
    =   (x:xs)++[]
    === x:(xs++[]) ? append_id_right xs
    *** QED

{-@ append_assoc :: xs:[a] -> ys:[a] -> zs:[a] -> { xs ++ (ys ++ zs) == (xs ++ ys) ++ zs } @-}
append_assoc :: [a] -> [a] -> [a] -> Proof
append_assoc [] ys zs = trivial
append_assoc (x:xs) ys zs
    =   (x:xs) ++ (ys ++ zs)
    === x:(xs ++ (ys ++ zs)) ? append_assoc xs ys zs
    *** QED

{-@ data Split a = Split {sl::[a], sx::a, sr::[a]}  @-}
data Split a = Split [a] a [a] 


{-@ reflect getL @-}
getL (Split l _ _ ) = l

{-@ reflect getX @-}
getX (Split _ x _ ) = x

{-@ reflect getR @-}
getR (Split _ _ r ) = r



{-@ type Digit a = {v:[a] | len v >= 1 && len v <= 4} @-}

-------------------------- MONOID
{-@ reflect measureList @-}
{-@ measureList :: 
        ap:(v -> v -> v)
    ->  e : v
    ->  mes:(a -> v) 
    ->  d:[a]
    ->  res:v @-}
measureList :: (v -> v -> v) -> v ->  (a -> v) -> [a] -> v
measureList ap e mes [] = e
measureList ap e mes (a:as) = mes a `ap` measureList ap e mes as

{-@ reflect splitDigitMon @-}
{-@ splitDigitMon ::
        ap:(v -> v -> v)
    ->  mes:(a -> v) 
    ->  p:(v -> Bool) 
    ->  i:v
    ->  d:Digit a
    ->  s:Split a @-}
splitDigitMon :: (v -> v -> v) -> (a -> v) -> (v -> Bool) -> v -> [a] -> Split a
splitDigitMon ap measure p i [a] = Split [] a []
splitDigitMon ap measure p i (a:as) 
    | p i' = Split [] a as
    | otherwise = let Split l x r = splitDigitMon ap measure p i' as in Split (a:l) x r
        where
            i' = ap i (measure a)


{-@ split_lemma_notp_mon :: 
       ap:(v -> v -> v)
    -> e : v
    -> assoc: (x:v -> y:v -> z:v -> {ap x (ap y z) = ap (ap x y) z})
    -> identity : (x:v-> {ap x e = x && ap e x = x})
    -> mes:(a -> v) 
    -> p:(v -> Bool)  
    -> i:v
    -> t:Digit a
    -> prnp:{ Proof | not (p i) } 
    -> prp:{ Proof | p (ap i (measureList ap e mes t)) } 
    -> { (not (p i) && p (ap i (measureList ap e mes t))) 
        => 
            not (p (ap i (measureList ap e mes (getL (splitDigitMon ap mes p i t)))))
        } / [len t] 
@-}
split_lemma_notp_mon ::  (v -> v -> v) -> v -> (v -> v -> v -> Proof) -> (v -> Proof) -> (a -> v) -> (v -> Bool) -> v -> [a] -> Proof -> Proof -> Proof 
split_lemma_notp_mon ap e assoc identity measure p i [a] prnp prp 
    =   not (p (i `ap` measureList ap e measure (getL (splitDigitMon ap measure p i [a]))))
    === not (p (i `ap` e)) ? identity i
    === not (p i)
    *** QED
split_lemma_notp_mon ap e assoc identity measure p i (a:as) prnp prp 
    | p i'
    =   not (p (i `ap` (measureList ap e measure (getL (splitDigitMon ap measure p i (a:as))))))
    === not (p (i `ap` e)) ? identity i
    === not (p i)
    *** QED 
    | not (p i')
    =   
        let 
            Split l x r = splitDigitMon ap measure p i' as 
            lemma_l 
                    =   p (ap i (measureList ap e measure (a:l)))
                    === p (ap i (ap (measure a) (measureList ap e measure l))) ? assoc i (measure a) (measureList ap e measure l) 
                    === p (ap (ap i (measure a)) (measureList ap e measure l))
                    *** QED
        in 
            (Split (a:l) x r ? 
                lemma_l
                &&&
                split_lemma_notp_mon 
                    ap 
                    e 
                    assoc 
                    identity 
                    measure 
                    p 
                    i' 
                    as 
                    (not (p i') *** QED) 
                    lemma_i_a_as_assoc   
            ) *** QED
            where
                i' = i `ap` measure a
                lemma_i_a_as_assoc 
                    =   p (ap i (measureList ap e measure (a:as)))
                    === p (ap i (ap (measure a) (measureList ap e measure as))) ? assoc i (measure a) (measureList ap e measure as) 
                    === p (ap (ap i (measure a)) (measureList ap e measure as))
                    *** QED

{-@ split_lemma_p_mon :: 
       ap:(v -> v -> v)
    -> e : v
    -> assoc: (x:v -> y:v -> z:v -> {ap x (ap y z) = ap (ap x y) z})
    -> identity : (x:v-> {ap x e = x && ap e x = x})
    -> mes:(a -> v) 
    -> p:(v -> Bool)  
    -> i:v
    -> t:Digit a
    -> prnp:{ Proof | not (p i) } 
    -> prp:{ Proof | p (ap i (measureList ap e mes t)) } 
    -> { (not (p i) && p (ap i (measureList ap e mes t))) 
        => 
            (p (ap (ap i (measureList ap e mes (getL (splitDigitMon ap mes p i t)))) (mes (getX (splitDigitMon ap mes p i t)))))
        } / [len t] 
@-}
split_lemma_p_mon ::  (v -> v -> v) -> v -> (v -> v -> v -> Proof) -> (v -> Proof) -> (a -> v) -> (v -> Bool) -> v -> [a] -> Proof -> Proof -> Proof 
split_lemma_p_mon ap e assoc identity measure p i [a] prnp prp 
    =   p (ap (ap i (measureList ap e measure (getL (splitDigitMon ap measure p i [a])))) (measure (getX (splitDigitMon ap measure p i [a]))))
    === p (ap (ap i (measureList ap e measure (getL (Split [] a [])))) (measure (getX (Split [] a []))))
    === p (ap (ap i (measureList ap e measure [])) (measure a))
    === p (ap (ap i e) (measure a)) ? identity i
    === p (ap i (measure a))
    === p (ap i (measure a)) ? identity (measure a)
    === p (ap i (ap (measure a) e))
    === p (ap i (measureList ap e measure [a]))
    *** QED
split_lemma_p_mon ap e assoc identity measure p i (a:as) prnp prp 
    | p i'
    =   p (ap (ap i (measureList ap e measure (getL (splitDigitMon ap measure p i (a:as))))) (measure (getX (splitDigitMon ap measure p i (a:as)))))
    === p (ap (ap i (measureList ap e measure (getL (Split [] a as)))) (measure (getX (Split [] a as))))
    === p (ap (ap i (measureList ap e measure [])) (measure a))
    === p (ap (ap i e) (measure a)) ? identity i
    === p (ap i (measure a))
    === p (ap i (measure a)) ? identity (measure a)
    === p (ap i (ap (measure a) e))
    === p (ap i (measureList ap e measure [a]))
    *** QED
    
    | not (p i')
    =   
        let recur = 
                let 
                    Split l x r = splitDigitMon ap measure p i' as 
                    lemma_l 
                            =   p (ap i (measureList ap e measure (a:l)))
                            === p (ap i (ap (measure a) (measureList ap e measure l))) ? assoc i (measure a) (measureList ap e measure l) 
                            === p (ap (ap i (measure a)) (measureList ap e measure l))
                            *** QED
                in 
                    Split (a:l) x r ? 
                        lemma_l
                        &&&
                        split_lemma_p_mon 
                            ap 
                            e 
                            assoc 
                            identity 
                            measure 
                            p 
                            i' 
                            as 
                            (not (p i') *** QED) 
                            lemma_i_a_as_assoc   
        in  p (i `ap` measureList ap e measure (getL (splitDigitMon ap measure p i (a:as))) `ap` measure (getX (splitDigitMon ap measure p i (a:as))) )
        === p (i `ap` measureList ap e measure (getL recur) `ap` measure (getX recur))
        *** QED
    where
        i' = i `ap` measure a
        lemma_i_a_as_assoc 
            =   p (ap i (measureList ap e measure (a:as)))
            === p (ap i (ap (measure a) (measureList ap e measure as))) ? assoc i (measure a) (measureList ap e measure as) 
            === p (ap (ap i (measure a)) (measureList ap e measure as))
            *** QED



--- OLD

{-@ split_lemma_p :: 
    p:([a] -> Bool) -> 
    i:[a] -> 
    {t:[a] | len t != 0 } -> 
    prnp:{ Proof | not (p i) } ->
    prp :{ Proof | p (i ++ t) } ->
    { (not (p i) && p (i ++ t)) 
        => 
            (p (i ++ getL (splitDigit p i t) ++ [getX (splitDigit p i t)] ) ) } / [len t] 
@-}
split_lemma_p :: ([a] -> Bool) -> [a] -> [a] -> Proof -> Proof -> Proof 
split_lemma_p p i [a] prnp prp
    =   p (i ++ getL (splitDigit p i [a]) ++ [getX (splitDigit p i [a])])
    === p (i ++ getL (Split [] a []) ++ [getX (Split [] a [])])
    === p (i ++ [] ++ [a]) ? append_assoc i [] [a]
    === p (i ++ ([] ++ [a]))
    === p (i ++ [a])
    *** QED
split_lemma_p p i (a:as) prnp prp
    | p i'
    =   p (i ++ getL (splitDigit p i (a:as)) ++ [getX (splitDigit p i (a:as))] )
    === p (i ++ getL (Split [] a as) ++ [getX (Split [] a as)])
    === p (i ++ [] ++ [a]) ? append_assoc i [] [a]
    === p (i ++ [a])
    *** QED
    | not (p i') =   
    let recur = let Split l x r = splitDigit p i' as in Split (a:l) x r ? help i a l &&& split_lemma_p p i' as (not (p i') *** QED) (app_lemma_help2 i a as) 
    in  p (i ++ getL (splitDigit p i (a:as)) ++ [getX (splitDigit p i (a:as))] )
    === p (i ++ getL recur ++ [getX recur])
    *** QED
        where
            i' = i ++ (a:[])

{-@ reflect splitDigit @-}
{-@ splitDigit :: p:([a] -> Bool) -> i:[a] -> {t:[a] | len t >= 1 } -> s:Split a @-}
splitDigit :: ([a] -> Bool) -> [a] -> [a] -> Split a
splitDigit p i [a] = Split [] a []
splitDigit p i (a:as) 
    | p i' = Split [] a as
    | otherwise = let Split l x r = splitDigit p i' as in Split (a:l) x r
        where
            i' = i ++ [a]


{-@ split_lemma_notp :: 
    p:([a] -> Bool) -> 
    i:[a] -> 
    {t:[a] | len t != 0 } -> 
    prnp:{ Proof | not (p i) } ->
    prp:{ Proof | p (i ++ t) } ->
    { (not (p i) && p (i ++ t)) 
        => 
            not (p (i ++ getL (splitDigit p i t))) } / [len t] 
@-}
split_lemma_notp :: ([a] -> Bool) -> [a] -> [a] -> Proof -> Proof -> Proof 
split_lemma_notp p i [a] prnp prp
    =   not (p (i ++ getL (splitDigit p i [a])))
    === not (p (i ++ [])) ? append_id_right i
    === not (p i)
    *** QED
split_lemma_notp p i (a:as) prnp prp
    | p i'
    =   not (p (i ++ getL (splitDigit p i (a:as))))
    === not (p (i ++ [])) ? append_id_right i
    === not (p i)
    *** QED 
    | not (p i')
    =   let Split l x r = splitDigit p i' as in Split (a:l) x r ? help i a l &&& split_lemma_notp p i' as (not (p i') *** QED) (app_lemma_help2 i a as)
    *** QED
        where
            i' = i ++ [a]
--((i ++ [a]) ++ l) == (i ++ cons a l
--((i <> mes a) <> mesList l) == (i <> mesList (a:l)

{-@ help :: i:[a] -> a:a -> l:[a] -> { ((i ++ [a]) ++ l) == (i ++ cons a l)  } @-}
help :: [a] -> a -> [a] -> Proof
help [] a l = trivial 
help (x:xs) a l
    =   (((x:xs) ++ [a]) ++ l) ? append_assoc (x:xs) [a] l
    === ((x:xs) ++ ([a] ++ l)) 
    === ((x:xs) ++ (a:l))
    === ((x:xs) ++ (a:l))
    === ((x:xs) ++ cons a l)
    *** QED


{-@ app_lemma_help2 :: i:[a] -> a:a -> as:[a] -> { (i ++ [a]) ++ as == i ++ (cons a as) } @-}
app_lemma_help2 :: [a] -> a -> [a] -> Proof
app_lemma_help2 []      a as
    =   ([] ++ [a]) ++ as
    === [a] ++ as
    === a:as
    === [] ++ (a:as)
    === [] ++ cons a as
    *** QED
app_lemma_help2 (x:xs)  a as
    =   ((x:xs) ++ [a]) ++ as
    === x:(xs ++ [a]) ++ as ? append_assoc xs [a] as
    === x:(xs ++ ([a] ++ as)) 
    === x:(xs ++ (a:as))
    === (x:xs) ++ (a:as) 
    === (x:xs) ++ cons a as 
    *** QED






main = do
    print 1