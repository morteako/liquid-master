abs :: Int -> Int
abs i | i >= 0 = i
      | i < 0 = negate i

abs' :: Int -> Int
abs' i | i >= 0 = i
       | not (i >= 0) = negate i

abs'' :: Int -> Int
abs'' i | i >= 0 = i
        | i < 0 = negate i
        | otherwise = error "should and won't ever happen"