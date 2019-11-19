{-@ LIQUID "--no-termination" @-}

import Proof ((?))

{-@ f :: a -> {v:a | True == False} @-}
f a = a ? f a

