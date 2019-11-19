
data Formula = 
        Var  Int
    |   Not  Formula
    |   And  Formula Formula
    |   Or   Formula Formula
    |   Impl Formula Formula


{-@ measure truthValue :: Int -> Bool @-}

{-@ measure isValid :: Formula -> Bool 
isValid (Var i) = truthValue i
isValid (Not s) = not (isValid s)
isValid (And l r) = isValid l && isValid r
isValid (Or l r) = isValid l || isValid r
isValid (Impl l r) = isValid l => isValid r
@-}


{-@ type Theorem = {v : Formula | isValid v} @-}

{-@ theo1 :: Theorem @-}
theo1 = Not (Not (Var 1) `And` (Var 1))


{-@ theo2 :: Theorem @-}
theo2 = Var 1 `Or` Not (Var 1)


{-@ theo3 :: Theorem @-}
theo3 = Var 1 `Impl` Var 1

{-@ theoremList :: [Theorem] @-}
theoremList = [theo1,theo2,theo3]

--Not allowed
-- {-@ nonTheo :: Theorem @-}
-- nonTheo = (Not (Var 1) `And` (Var 1))