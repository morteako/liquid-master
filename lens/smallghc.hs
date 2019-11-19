{-@ ix2 :: i:Nat -> (forall f . Functor f => (a -> f a) -> [a] -> f [a]) @-} 
ix2 :: Int -> Lens [a] [a] a a
ix2 n afb xs = let (pre,x,post) = split n xs in fmap (\y -> pre ++ y:post) (afb x)
