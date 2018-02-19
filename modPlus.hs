import Language.Haskell.Liquid.ProofCombinators

{-@ type Nat = {x:Int | x >= 0} @-}

{-@ modPlus :: n:Nat -> {x:Nat | x < n} -> {y:Nat | y < n} -> {r:Nat | x+y<2*n && r < n && r >= 0} @-}
modPlus n x y = if x + y >= n then x + y - n  else x+y ::Int

{-@ reflect modPlus @-}

{-@ modIdLeft :: n:Nat -> {x:Nat | x < n} -> {r:Nat | x == r} @-}
modIdLeft n x = modPlus n 0 x


{-@ modIdRight :: n:Nat -> {x:Nat | x < n} -> {r:Nat | x == r} @-}
modIdRight n x = modPlus n x 0

{-@ reflect modInv @-}
{-@ modInv :: n:Nat -> {x:Nat | x < n} -> {r:Nat | r >= 0 && r < n} @-}
modInv n x = if x == 0 then 0 else n - x :: Int


{-@ rightInv ::  n:Nat -> {x:Nat | x < n} -> {modPlus n x (modInv n x) == 0} @-}
rightInv n x = modPlus n x (modInv n x) ==. n - n ==. 0 *** QED

{-@ leftInv ::  n:Nat -> {x:Nat | x < n} -> {modPlus n (modInv n x) x  == 0} @-}
leftInv n x = modPlus n (modInv n x) x ==. n - n ==. 0 *** QED

{-@ com :: 
	n:Nat -> 
	{x:Nat | x < n} -> 
	{y:Nat | y < n} -> 
	{modPlus n x y == modPlus n y x} @-}
com :: Int -> Int -> Int -> Proof
com n x y = modPlus n x y ==. modPlus n y x *** QED
--	| x + y >= n = modPlus n x y ==. modPlus n y x *** QED
--	| otherwise = modPlus n x y ==. modPlus n y x *** QED


{-@ asso :: 
	n:Nat -> 
	{x:Nat | x < n} -> 
	{y:Nat | y < n} -> 
	{z:Nat | z < n} -> 
	{modPlus n x (modPlus n y z) == modPlus n (modPlus n x y) z} @-}
asso :: Int -> Int -> Int -> Int -> Proof
asso n x y z 
	| x + y + z < n = 
		modPlus n x (modPlus n y z) ==. 
		modPlus n x (y + z) ==. 
		x + (y + z) ==.
		(x + y) + z ==.
		modPlus n (x + y) z ==.
		modPlus n (modPlus n x y) z *** QED
	| x + y + z >= 2*n =
		modPlus n x (modPlus n y z) ==. 
		x + (y + z - n) - n ==.
		(x + y - n) + z - n ==.
		modPlus n (modPlus n x y) z *** QED
	| x + y >= n && y + z < n =
		modPlus n x (modPlus n y z) ==. 
		modPlus n x (y + z) ==.
		x + (y + z) - n ==.
		(x+y-n) + z ==.	
		modPlus n (x+y-n) z ==.
		modPlus n (modPlus n x y) z *** QED
	| x + y + z < 2*n && x + y >= n && y + z >= n =
		modPlus n x (modPlus n y z) ==. 
		modPlus n x (y + z - n) ==.
		x + (y + z) - n ==.
		(x+y-n) + z ==.	
		modPlus n (x+y-n) z ==.
		modPlus n (modPlus n x y) z *** QED
	| x + y < n && y + z >= n =
		modPlus n x (modPlus n y z) ==. 
		modPlus n x (y + z - n) ==.
		x + y + z - n ==.
		modPlus n (x+y) z ==.
		modPlus n (modPlus n x y) z *** QED
	| x+y<n && y+z<n && x + y + z >= n = 
		modPlus n x (modPlus n y z) ==. 
		modPlus n x (y + z) ==.
		x + y + z - n ==.
		modPlus n (x+y) z ==.
		modPlus n (modPlus n x y) z *** QED

{-@ assoF :: 
 n:Nat -> 
 {x:Nat | x < n} -> 
 {y:Nat | y < n} -> 
 {z:Nat | z < n} ->
 {v:Nat | v == 0}
@-}
assoF :: Int -> Int -> Int -> Int -> Int
assoF n x y z = (modPlus n (modPlus n x y) z) - (modPlus n x (modPlus n y z))
