


{-@ LIQUID "--ple" @-}
{-@ LIQUID "--no-adt"         @-}
{-@ LIQUID "--reflection"     @-}



{-# LANGUAGE RankNTypes #-}

import Language.Liquid.Haskell.ProofCombinators

-- {-@ reflect un @-}
-- {-@ lazy un @-}
-- un = un

{-@ reflect constfmap @-}
{-@ constfmap :: f:(a -> b) -> c:Const m a -> cc:Const m c  @-}
constfmap :: (a -> b) -> Const m a -> Const m c
constfmap f (Const a) = Const a


{-@ data Const a b = Const {unConst :: a} @-}
data Const a b = Const {unConst :: a}

 
{-@ data D = A | B  @-}
data D = A | B deriving Show

type FLens s t a b = forall f. (forall a b . (a -> b) -> f a -> f b) -> (a -> f b) -> s -> f t
type FLens' s a = FLens s s a a

{-@ data DPair = DPair {x :: D, y :: D} @-}
data DPair = DPair {x :: D, y :: D} deriving Show

{-@ reflect dpairFlipped @-}
{-@ dpairFlipped :: D -> D -> DPair  @-}
dpairFlipped :: D -> D -> DPair
dpairFlipped y x = DPair x y

{-@ reflect xLens @-}
{-@  xLens :: FLens' DPair D @-} 
xLens :: FLens' DPair D
xLens fmap afb (DPair xx yy) = fmap (dpairFlipped yy) (afb xx)


{-@ reflect view @-}
view :: FLens s t a b -> s -> a
view lens s = unConst (lens constfmap Const s)

{-@ type LensProof1 s a = noe:FLens' s a -> v:a -> s:s -> { view xLens (set xLens v s) == v} @-}

{-@ safeView :: lens:FLens' s a -> p:LensProof1 s a  -> s:s -> v:a @-}
safeView :: FLens' s a -> (FLens' s a -> a -> s -> Proof) -> s -> a
safeView lens proof = view lens


-- {-@ safeView2 :: ss:DPair -> {lens:FLens' DPair D | view lens ss == A} -> {v:D | v == A} @-}
-- safeView2 :: DPair -> FLens' DPair D -> D
-- safeView2 s lens = unConst (lens constfmap Const s) ? view lens s




test1 = safeView xLens (\_ -> xLens_1) (DPair B B)

-- test2 = safeView2 (DPair B B) xLens
-- test2 = safeView xLensBad (DPair A B)


-- 
-- {-@ tf :: {f : (Bool -> Bool) | f True == True } -> b:Bool @-}
-- tf :: (Bool -> Bool) -> Bool
-- tf f = f True


-- {-@ testf :: b:Bool -> {v:Bool | b == True => v == True } @-}
-- testf True = True
-- testf False = True

-- ttt = tf testf

{-@ step0 :: x:D -> y:D -> { view xLens (DPair x y) == unConst (xLens constfmap Const (DPair x y)) } @-}
step0 :: D -> D -> Proof
step0 x y 
    = trivial

-- {-@ xLens_view_lemma :: x:D -> y:D -> { view xLens (DPair x y) == x} @-}
-- xLens_view_lemma :: D -> D -> Proof
-- xLens_view_lemma x y 
--     =   view xLens (DPair x y) ? step0 x y
--     ==. unConst (xLens constfmap Const (DPair x y))
--     ==. unConst (constfmap (dpairFlipped y) (Const x)) 
--     ==. unConst (Const x) 
--     ==. x
--     *** QED

{-@ xLens_view_lemma_2 :: x:D -> y:D -> { view xLens (DPair x y) == x} @-}
xLens_view_lemma_2 :: D -> D -> Proof
xLens_view_lemma_2 x y 
    = trivial 

{-@ type V lens = s:s -> v:a -> { view xLens (set xLens v s) == v } @-}


{-@ reflect set @-}
{-@ set :: lens:FLens s t a b -> v:b -> val:s -> res:t @-}
set :: FLens s t a b -> b -> s -> t
set lens b s = runIdentity (lens idfmap (constIdentity b) s)


-- {-@ reflect viewD @-}
-- viewD :: FLens DPair DPair D D -> DPair -> D
-- viewD lens (DPair a b) = a

-- {-@ xLens_2 :: v:D -> s:DPair -> { view xLens s == v}  @-}
-- xLens_2 :: D -> DPair -> Proof
-- xLens_2 i s@(DPair xx yy) =
--     un *** QED
    


    
{-@ data Identity a = Identity {runIdentity :: a} @-}
data Identity a = Identity {runIdentity :: a}

{-@ reflect idfmap @-}
{-@ idfmap :: f:(a -> b) -> ia:Identity a -> ib:Identity b @-}
idfmap :: (a -> b) -> Identity a -> Identity b
idfmap f (Identity a) = Identity (f a)

{-@ reflect constIdentity @-}
{-@ constIdentity :: x:a -> v:b -> r:Identity a @-}
constIdentity :: a -> b -> Identity a
constIdentity a _ = Identity a

{-@ xLens_1 :: v:D -> s:DPair -> { view xLens (set xLens v s) == v}  @-}
xLens_1 :: D -> DPair -> Proof
xLens_1 i s@(DPair xx yy)
    = trivial
    -- =   view xLens (set xLens i s) 
    -- === view xLens (runIdentity (xLens idfmap (constIdentity i) s)) 
    -- === view xLens (runIdentity (idfmap (dpairFlipped yy) ((constIdentity i) s))) 
    -- === view xLens (runIdentity (idfmap (dpairFlipped yy) (Identity i)))  
    -- === view xLens (runIdentity (Identity (DPair i yy))) 
    -- === view xLens (DPair i yy)  
    -- === view xLens (runIdentity (idfmap (dpairFlipped yy) (Identity i))) 
    -- === view xLens (runIdentity (Identity (DPair i yy))) 
    -- === view xLens (DPair i yy) 

    -- *** QED

{-@ xLens_2 :: s:DPair -> { set xLens (view xLens s) s == s}  @-}
xLens_2 :: DPair -> Proof
xLens_2  s@(DPair xx yy) = trivial

{-@ xLens_3 :: v:D -> vv:D -> s:DPair -> { set xLens vv (set xLens v s) == set xLens vv s }  @-}
xLens_3 :: D -> D -> DPair -> Proof
xLens_3 _ _ _ = trivial

{-@ reflect sLensHelp @-}
sLensHelp x = Identity True

{-@ reflect sLens @-}
sLens :: FLens' (Identity Bool) Bool
sLens fmap afb s = fmap sLensHelp (afb True)



-- {-@ assume verify_lens :: Eq a => lens:FLens' s a -> v:a -> s:s -> { b : Bool | b <=> verified lens } @-}
-- verify_lens :: Eq a => FLens' s a -> a -> s -> Bool
-- verify_lens lens v s = view lens (set lens v s) == v 

{-@ reflect verify_lens2 @-}
{-@ verify_lens2 :: Eq a => FLens' s a -> a -> s -> Bool @-}
verify_lens2 :: Eq a => FLens' s a -> a -> s -> Bool
verify_lens2 lens v s = view lens (set lens v s) == v


-- {-@ measure checked :: FLens' s a -> Bool@-}

{-@ type VL s a = {lens: FLens' s a | verify_lens lens B (DPair B B)} @-}

{-@ type VL2 s a = {lens: FLens' s a | verify_lens2 lens viewVal setVal } @-}

{-@ type VL3 s a sval vval = {lens : FLens' s a | view lens (set lens vval sval) == vval} @-}

{-@ xx :: VL2 DPair D @-}
xx :: FLens' DPair D
xx = xLens

--UNSAFE AS EXPECTED. GOOD
-- {-@ xLensBad_1 :: v:D -> s:DPair -> { view xLensBad (set xLens v s) == v}  @-}
-- xLensBad_1 :: D -> DPair -> Proof
-- xLensBad_1 i s@(DPair xx yy)
--     = trivial


{-@  xLensBad :: VL2 DPair D @-} 
xLensBad :: FLens' DPair D
xLensBad fmap afb (DPair xx yy) = fmap (dpairFlipped A) (afb A)

{-@ reflect val1 @-}
{-@ lazy val1 @-}
val1 :: a
val1 = val1

{-@ reflect val2 @-}
{-@ lazy val2 @-}
val2 :: a
val2 = val2

{-@ measure viewVal :: a @-}
{-@ measure setVal  :: a @-}

-- {-@ viewset :: lens:FLens s t a b -> { view lens ( set lens val1 val2) == val1 } @-}
-- viewset :: FLens s t a b -> Proof
-- viewset lens = un




{-@ type VerifiedLens s a = { l:FLens s s a a | view lens setVal == view lens viewVal } @-}

{-@ pp :: VerifiedLens DPair D @-}
pp :: FLens' DPair D
pp = xLens

-- {-@ l :: V xLens @-}
-- l :: s -> s -> a -> Proof
-- l s ss v = trivial

-- {-@ type VV lens = sVal:s -> vVal:a -> { view lens sVal == view lens sVal } @-}

-- {-@ ll :: VV xLens @-}
-- ll :: s -> a -> Proof
-- ll s v = trivial

main = do
    print 1