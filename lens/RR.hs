{-@ LIQUID "--reflection"           @-}
-- {-@ LIQUID "--no-adt"               @-}
-- {-@ LIQUID "--prune-unsorted"      @-}


{-# LANGUAGE RankNTypes #-}

type Lens s t a b = forall f. Functor f => (a -> f b) -> s -> f t


{-@ data ReLens s t a b  <p :: s -> Bool> = ReLens (Lens s<p> t a b) @-}
data ReLens s t a b = ReLens {getReLens ::(Lens s t a b)}    

{-@ data ReLens' s t a b  <p :: s -> t -> Bool> = ReLens' (Lens (src:s) t<p src> a b) @-}
data ReLens' s t a b = ReLens' {getReLens' ::(Lens s t a b)}    


-- {-@ ix2 :: i:Nat -> ReLens <{\s t -> len s > i && len s == len t}> [a] [a] a a @-}
{-@ ix2 :: i:Nat -> ReLens <{\x -> len x > i}> [a] [a] a a @-}
ix2 :: Int -> ReLens [a] [a] a a
ix2 n = ReLens (func n)
    where
      {-@ func :: i:Nat -> _ -> {xs:_ | len xs > i} -> f {v:_ | len v == len xs} @-}
      func i afb xs = let (pre, x, post) = split i xs in fmap (\y -> pre ++ y:post) (afb x)

{-@ split :: i:Nat -> {xs:[a] | i < len xs} -> ({v:[a] | len v == i}, a, {v:[a] | i + 1 + len v == len xs}) @-}
split :: Int -> [a] -> ([a],a,[a])
split n xs =  (pre, p, post)
  where
    (pre, p:post) = splitAt n xs

{-@ assume splitAt :: n:Nat -> {xs:[a] | n < len xs} -> ({v:[a] | len v == n}, {v:[a]| n + len v = len xs}) @-}





{-@ ix :: i:Nat -> ReLens <{\x -> len x > i}> [a] [a] a a @-}
ix :: Int -> ReLens [a] [a] a a
ix n = ReLens (\afb xs -> let (pre,x,post) = split n xs in fmap (\y -> pre ++ y:post) (afb x))


-- {-@ split :: i:Nat -> {xs:[a] | len xs > i} -> ([a],a,[a]) @-}
-- split :: Int -> [a] -> ([a],a,[a])
-- split n xs = (pre,p,post)
--     where
--         (pre,p:post) = splitAt n xs



-- {-@ data ReLens s a  <p :: s -> Bool> = ReLens (Lens s<p> s a a) @-}
-- data ReLens s a = ReLens {getReLens ::(Lens s s a a)}    

-- {-@ data RefLens s t a b  <sp :: s -> Bool, p :: s -> t -> Bool> = 
--     RefLens (Lens (source:s) t<p source> a b) @-}
-- data RefLens s t a b = RefLens {getRefLens ::(Lens s t a b)}    

-- {-@ data ListLens' a <p :: [a] -> Bool> 
-- = ListLens ((a -> f a) -> xs:[a]<p> -> f {t:[a] | len xs == len t}) @-}
-- data ListLens' a = ListLens ((a -> f a) -> [a] -> f [a])