{-@ LIQUID "--reflection" @-}

import Proof

data Peano = Zero | Succ Peano

{-@ reflect add @-}
add :: Peano -> Peano -> Peano
add Zero b = b
add (Succ a) b = Succ (add a b)

{-@ addIdRight :: a:Peano -> { add a Zero == a } @-}
addIdRight Zero = add Zero Zero === Zero *** QED
addIdRight (Succ s) 
    =   add (Succ s) Zero
    === Succ (add s Zero) ? addIdRight s
    === Succ s
    *** QED


{-@ addSucc :: a:Peano -> b:Peano -> {Succ (add a b) == add a (Succ b)} @-}
addSucc Zero b
    =   Succ (add Zero b)
    === Succ b
    === add Zero (Succ b) 
    *** QED
addSucc (Succ a) b
    =   Succ (add (Succ a) b)
    === Succ (Succ (add a b)) ? addSucc a b
    === Succ (add a (Succ b))
    === add (Succ a) (Succ b)
    *** QED

{-@ addComm :: a:Peano -> b:Peano -> {add a b == add b a } @-}
addComm Zero b
    =   add Zero b
    === b ? addIdRight b
    === add b Zero
    *** QED
addComm (Succ a) b
    =   add (Succ a) b
    === Succ (add a b) ? addComm a b
    === Succ (add b a) ? addSucc b a
    === add b (Succ a)
    *** QED


