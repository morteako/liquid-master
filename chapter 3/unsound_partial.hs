{-@ LIQUID "--no-totality" @-}

import Proof

{-@ f :: b:Bool -> {v:Bool | v == False && b == v} @-}
f False = False

{-@ g :: b:Bool -> {v:Bool | v == True && b == v} @-}
g True = True

{-@ unsound :: Bool -> { True == False } @-}
unsound True = () ? f True
unsound False = () ? g False 