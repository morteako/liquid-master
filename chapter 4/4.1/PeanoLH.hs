{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

import Proof

data Peano = Zero | Succ Peano

{-@ reflect add @-}
add :: Peano -> Peano -> Peano
add Zero b = b
add (Succ a) b = Succ (add a b)


{-@ addIdRight :: a:Peano -> { add a Zero == a } @-}
addIdRight Zero = trivial
addIdRight (Succ s) = addIdRight s


{-@ addSucc :: a:Peano -> b:Peano -> { Succ (add a b) == add a (Succ b)} @-}
addSucc :: Peano -> Peano -> Proof
addSucc Zero b
    =   trivial
addSucc (Succ a) b
    =   addSucc a b

{-@ addComm :: a:Peano -> b:Peano -> { add a b == add b a } @-}
addComm Zero b
    =   addIdRight b
addComm (Succ a) b
    =   addComm a b &&& addSucc b a
