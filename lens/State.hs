

{-@ data State s a <p :: s -> s -> Bool> = State (v:s -> (a,s<p v>)) @-}
data State s a = State (s -> (a,s))

instance Functor (State s) where
    fmap f (State g) = State (\s -> 
        let (a,s) = g s in (f a, s))

instance Applicative (State s) where
    pure s = State (\x -> (s,x))
    fs <*> as = do
        f <- fs
        a <- as
        pure (f a)

instance Monad (State s) where
    (State f) >>= (atoS) = State $ \s ->
        case f s of (a,s) -> case atoS a of State g -> g s


put :: s -> State s ()
put s = State (\_ -> ((),s))

{-@ type IntState a = State <{\s1 s2 -> s1 <= s2}> Int a  @-}
type IS a = State Int a

-- {-@ runState :: s -> State s a @-}
-- runState :: s -> State s a -> (a,s)
-- runState s (State f) = f s

-- {-@ assume startState :: s -> State s () <p :: s -> s -> Bool> @-}
-- startState s = put s

-- {-@ assume runState :: s -> State s () @-}
-- runState :: s -> State s ()
-- runState s  = State (\_ -> ((),s))

{-@ inc :: IntState () @-}
inc ::  State Int ()
inc = State (\s -> ((),s+1))



{-@ is :: IntState () @-}
is :: IS ()
is = do
    inc

    
{-@ data State' s a <pin :: s -> Bool,prel :: s -> s -> Bool> = 
    State' (v:s<pin> -> (a,s<p v>)) @-}
data State' s a = State' (s -> (a,s))

{-@ data State s a <p :: s -> s -> Bool> = State (v:s -> (a,s<p v>)) @-}
data State s a = State (s -> (a,s))

instance Functor (State s) where
    fmap f (State g) = State (\s -> 
        let (a,s) = g s in (f a, s))

instance Applicative (State s) where
    pure s = State (\x -> (s,x))
    fs <*> as = do
        f <- fs
        a <- as
        pure (f a)

instance Monad (State s) where
    (State f) >>= (atoS) = State $ \s ->
        case f s of (a,s) -> case atoS a of State g -> g s

{-@ assume bind :: 
    forall s <p :: s -> s -> Bool> . State <p> s a -> (a -> State <p> s b) -> State <p> s b @-}
bind :: State s a -> (a -> State s b) -> State s b
bind s f = s >>= f

{-@ assume comb :: forall s <p :: s -> s -> Bool> . State <p> s a -> State <p> s b  -> State <p> s b @-}
comb :: State s a -> State s b -> State s b
comb s b = s >> b

-- {-@ infix >> @-}
-- {-@ using ((>>)) as  a -> a -> a} @-}

{-@ type IntState a = State <{\s1 s2 -> s1 <= s2}> Int a  @-}

type IS a = State Int a

{-@ inc :: IntState () @-}
inc ::  State Int ()
inc = modify (+1)

{-@ assume put :: forall s <prel :: s -> s -> Bool,p :: s -> Bool> . s<p> -> State <prel> s<p> ()  @-}
put :: s -> State s ()
put s = State (\_ -> ((),s))

{-@ assume get :: forall s <prel :: s -> s -> Bool,p :: s -> Bool> .State <prel> s<p> s<p> @-}
get :: State s s
get = State (\s -> (s,s))

{-@ is :: IntState () @-}
is :: IS ()
is = 
    inc `comb` inc `comb` inc 

{-@ is2 :: IntState () @-}
is2 :: IS ()
is2 = 
    modify (+1) `comb` modify (+5) `comb` modify (*1)

{-@ is4 :: IntState () @-}
is4 :: IS ()
is4 = 
    -- get `bind` \s -> put s
    put 5 `comb` put 4
    
        
    
-- FIKS modify til å fungere på staten. NatState

{-@ modify :: forall s <p :: s -> s -> Bool,ps :: s -> Bool> . (a:s -> s<p a>) -> State <p> s () @-}
modify :: (s -> s) -> State s ()
modify f = State $ \s -> ((),f s)

{-@ type NatState a = State Nat a  @-}
{-@ type NatSt s a = State <{\x -> x > 0}> s a  @-}

{-@ runState :: State s a -> s -> s @-}
runState (State f) s = snd $ f s 


{-@ runStateNat :: State Nat a -> Nat -> Nat @-}
runStateNat :: State Int a -> Int -> Int
runStateNat (State f) s = snd $ f s 

{-@ stateNatTest :: Nat @-}
stateNatTest = runStateNat (put 10) 5

--Fungerer ikke, selv med assumes på get og put
-- {-@ stateNatTest2 :: Nat @-}
-- stateNatTest2 = runStateNat (put 10 `comb` get) 5