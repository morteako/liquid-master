{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TemplateHaskell #-}

import Control.Lens
import Control.Lens.Tuple

type Lens s t a b = forall f. Functor f => (a -> f b) -> s -> f t
type SimpleLens s a = forall f. Functor f => (a -> f a) -> s -> f s

class SInd index s where
    sindexLens :: forall f. Functor f => (index -> f index) -> s -> f s

instance SInd index s => Ind index index s s where
    indexLens = sindexLens

class Ind index b s t where
    indexLens :: Functor f => (index -> f b) -> s -> f t
    

data IntAndString = IS Int String deriving Show

data MaybeIntAndString = LIS {_intM :: Maybe Int, _stringM :: Maybe String } deriving Show
makeLenses ''MaybeIntAndString

data D = D {_is :: IntAndString, _lis :: MaybeIntAndString} deriving Show
makeLenses ''D

instance SInd IntAndString D where
    sindexLens = is

instance SInd MaybeIntAndString D where
    sindexLens = lis

instance SInd (Maybe Int) MaybeIntAndString where
    sindexLens = intM

instance SInd (Maybe String) MaybeIntAndString where
    sindexLens = stringM

intLens afa (IS i s) = fmap (\newI -> IS newI s) (afa i)
stringLens afa (IS i s) = fmap (\newS -> IS i newS) (afa s)

instance SInd Int IntAndString where
    sindexLens = intLens

instance SInd String IntAndString where
    sindexLens = stringLens



-- instance Ind a c (a,b) (c,b) where
--     indexLens = fstLens

-- instance Ind b (a,b) where
--     indexLens = sndLens

fstLens afa (a,b) = fmap (\x -> (x,b)) (afa a)
sndLens afa (a,b) = fmap (\x -> (a,x)) (afa b)

indover :: SInd a s => (a -> a) -> s -> s
indover f s = over sindexLens f s

inc :: Int -> Int
inc n = n+1

yell :: String -> String
yell str = str ++ "!"

main = do
    print $ over _1 show (1,2)
    
    print $ over intLens (+1) (IS 1 "hei")
    print $ over stringLens reverse (IS 1 "hei")
    
    print $ inc ((IS 1 "hei") ^. sindexLens)
    print $ yell ((IS 1 "hei") ^. sindexLens)

    print $ indover inc (IS 2 "hei")
    print $ indover yell (IS 2 "hei")
    
    print $ indover inc (IS 2 "hei")
    print $ indover yell (IS 2 "hei")

    print $ over (sindexLens . sindexLens) inc (D (IS 1 "hei") (LIS Nothing Nothing))



