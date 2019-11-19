{-# LANGUAGE RankNTypes #-}

type Lens s t a b = forall f. Functor f => (a -> f b) -> s -> f t

{-@ ix :: i:Nat -> Lens [a] [a] a a @-}
ix :: Int -> Lens [a] [a] a a
ix n = func n
    where
        {-@ assume func :: forall f . Functor f => i:Nat -> (a -> f a) -> {xs:[a] | len xs > i} -> ys:f {v:[a] | len v == len xs} @-}
        func i afb xs = let (pre,x,post) = split i xs in fmap (\y -> pre ++ y:post) (afb x)


{-@ split :: i:Nat -> {xs:[a] | len xs > i} -> ([a],a,[a]) @-}
split :: Int -> [a] -> ([a],a,[a])
split n xs = (pre,p,post)
    where
    (pre,p:post) = splitAt n xs

-- LiquidHaskell Version 0.8.6.0, Git revision f4fe82cd03fbe906379c8ebeac5ec3efae0b4cd8 [develop@f4fe82cd03fbe906379c8ebeac5ec3efae0b4cd8 (Mon Jun 24 10:55:17 2019 +0200)]
-- Copyright 2013-19 Regents of the University of California. All Rights Reserved.

-- Targets: ghcBug.hs

-- **** [Checking: ghcBug.hs] *****************************************************

-- **** DONE:  A-Normalization ****************************************************

-- liquid: liquid: panic! (the 'impossible' happened)
--   (GHC version 8.6.5 for x86_64-unknown-linux):
--         piResultTys1
--   *
--   [a_xo]
--   Call stack:
--       CallStack (from HasCallStack):
--         callStackDoc, called at compiler/utils/Outputable.hs:1160:37 in ghc:Outputable
--         pprPanic, called at compiler/types/Type.hs:1022:5 in ghc:Type

-- Please report this as a GHC bug:  http://www.haskell.org/ghc/reportabug
