{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}


import Prelude hiding ((++))
import Proof

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

--BECAUSE OF WEIRD SORT ERROR x:xs == [x] ++ xs
{-@ append_cons_left :: x:a -> xs:[a] -> { cons x xs == [x] ++ xs } @-}
append_cons_left :: a -> [a] -> Proof
append_cons_left x xs = trivial

{-@ reflect cons @-}
{-@ cons :: x:a -> xs:[a] -> xxs:[a] @-}
cons x xs = x:xs


{-@ data Split a = Split {sl::[a], sx::a, sr::[a]}  @-}
data Split a = Split [a] a [a] 

{-@ reflect un @-}
un = un



{-@ reflect splitDigit @-}
{-@ splitDigit :: p:([a] -> Bool) -> i:[a] -> {t:[a] | len t >= 1 } -> s:Split a @-}
splitDigit :: ([a] -> Bool) -> [a] -> [a] -> Split a
splitDigit p i [a] = Split [] a []
splitDigit p i (a:as) 
    | p i' = Split [] a as
    | otherwise = let Split l x r = splitDigit p i' as in Split (a:l) x r
        where
            i' = i ++ [a]

{-@ reflect getL @-}
getL (Split l _ _ ) = l

{-@ reflect getX @-}
getX (Split _ x _ ) = x

{-@ reflect getR @-}
getR (Split _ _ r ) = r



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
    =   not (p (i ++ getL (splitDigit p i (a:as))))
    === not (p (i ++ getL (let Split l x r = splitDigit p i' as in Split (a:l) x r ? help i a l &&& split_lemma_notp p i' as (not (p i') *** QED) (app_lemma_help2 i a as) )))
    *** QED
        where
            i' = i ++ [a]


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
    | not (p i')
    =   
    let recur = let Split l x r = splitDigit p i' as in Split (a:l) x r ? help i a l &&& split_lemma_p p i' as (not (p i') *** QED) (app_lemma_help2 i a as) 
    in  p (i ++ getL (splitDigit p i (a:as)) ++ [getX (splitDigit p i (a:as))] )
    === p (i ++ getL recur ++ [getX recur])
    *** QED
        where
            i' = i ++ (a:[])

{-@ split_lemma_app :: 
    p:([a] -> Bool) -> 
    i:[a] -> 
    {t:[a] | len t != 0 } -> 
    prnp:{ Proof | not (p i) } ->
    prp :{ Proof | p (i ++ t) } ->
    { (not (p i) && p (i ++ t)) 
        => 
            getL (splitDigit p i t) ++ [getX (splitDigit p i t)] ++ getR (splitDigit p i t) == t } / [len t] 
@-}
split_lemma_app :: ([a] -> Bool) -> [a] -> [a] -> Proof -> Proof -> Proof 
split_lemma_app p i [a] prnp prp 
    =   getL (splitDigit p i [a]) ++ [getX (splitDigit p i [a])] ++ getR (splitDigit p i [a])  
    === getL (Split [] a []) ++ [getX (Split [] a [])] ++ getR (Split [] a [])
    === [] ++ [a] ++ [] ? append_id_right [a] 
    === [a]
    *** QED
split_lemma_app p i (a:as) prnp prp
    | p i'
    =   getL (splitDigit p i (a:as)) ++ [getX (splitDigit p i (a:as))] ++ getR (splitDigit p i (a:as))  
    === getL (Split [] a as) ++ [getX (Split [] a as)] ++ getR (Split [] a as)  
    === [] ++ [a] ++ as
    === (a:as)
    *** QED
    | not (p i')
    =
    let recur = let Split l x r = splitDigit p i' as in Split (a:l) x r ? app_help a as l x r &&& help i a l &&& split_lemma_app p i' as (not (p i') *** QED) (app_lemma_help2 i a as) 
    in  getL (splitDigit p i (a:as)) ++ [getX (splitDigit p i (a:as))] ++ getR (splitDigit p i (a:as)) 
    ===  getL recur ++ [getX recur] ++ getR recur 
    === cons a as
    === a:as
    *** QED
    where
        i' = i ++ [a]



{-@ split_lemma :: 
    p:([a] -> Bool) -> 
    i:[a] -> 
    {t:[a] | len t != 0 } -> 
    prnp:{ Proof | not (p i) } ->
    prp :{ Proof | p (i ++ t) } ->
    { (not (p i) && p (i ++ t)) 
        => 
            (getL (splitDigit p i t) ++ [getX (splitDigit p i t)] ++ getR (splitDigit p i t) == t )
            &&
            (p (i ++ getL (splitDigit p i t) ++ [getX (splitDigit p i t)] ) )
            &&
            (not (p (i ++ getL (splitDigit p i t))))
    } / [len t] 
@-}
split_lemma :: ([a] -> Bool) -> [a] -> [a] -> Proof -> Proof -> Proof 
split_lemma p i as prnp prp = 
    toProof (split_lemma_app p i as prnp prp)
    &&&
    toProof (split_lemma_notp p i as prnp prp)
    &&&
    toProof (split_lemma_p p i as prnp prp)

{-@ app_help :: 
    a:a -> 
    as:[a] -> 
    l:[a] -> 
    x:a -> 
    r:[a] -> 
    {  l ++ [x] ++ r == as => (cons a l) ++ [x] ++ r = cons a as } @-}
app_help :: a -> [a] -> [a] -> a -> [a] -> Proof
app_help a as l x r = trivial





main = do
    print 1