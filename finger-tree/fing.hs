{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

{-@ LIQUID "--no-termination" @-}

infixr 5 ><
infixr 5 <|, :<
infixl 5 |>, :>

-- | View of the left end of a sequence.
data ViewL s a
    = EmptyL        -- ^ empty sequence
    | a :< s a      -- ^ leftmost element and the rest of the sequence
    deriving (Eq, Ord, Show, Read)

-- | View of the right end of a sequence.
data ViewR s a
    = EmptyR        -- ^ empty sequence
    | s a :> a      -- ^ the sequence minus the rightmost element,
                    -- and the rightmost element
    deriving (Eq, Ord, Show, Read)

instance (Functor s) => Functor (ViewL s) where
    fmap _ EmptyL    = EmptyL
    fmap f (x :< xs) = f x :< fmap f xs

instance (Functor s) => Functor (ViewR s) where
    fmap _ EmptyR    = EmptyR
    fmap f (xs :> x) = fmap f xs :> f x

instance (Measured v a) => Semigroup (FingerTree v a) where
    (<>) = (><)

-- | 'empty' and '><'.
instance (Measured v a) => Monoid (FingerTree v a) where
    mempty = empty


{-@ measure digitSize @-}
digitSize :: Digit a -> Int
digitSize (One {}) = 1
digitSize (Two {}) = 2
digitSize (Three {}) = 3
digitSize (Four {}) = 4


data Digit a
    = One a
    | Two a a
    | Three a a a
    | Four a a a a
    deriving (Show)

instance Foldable Digit where
    foldMap f (One a) = f a
    foldMap f (Two a b) = f a `mappend` f b
    foldMap f (Three a b c) = f a `mappend` f b `mappend` f c
    foldMap f (Four a b c d) = f a `mappend` f b `mappend` f c `mappend` f d



-------------------
-- 4.1 Measurements
-------------------

-- | Things that can be measured.
class (Monoid v) => Measured v a | a -> v where
    measure :: a -> v

instance (Measured v a) => Measured v (Digit a) where
    measure = foldMap measure

---------------------------
-- 4.2 Caching measurements
---------------------------
{-@ measure nodeSize @-}
nodeSize :: Node v a -> Int
nodeSize Node2{} = 2
nodeSize Node3{} = 3

data Node v a = Node2 !v a a | Node3 !v a a a
    deriving (Show)

instance Foldable (Node v) where
    foldMap f (Node2 _ a b) = f a `mappend` f b
    foldMap f (Node3 _ a b c) = f a `mappend` f b `mappend` f c

node2        ::  (Measured v a) => a -> a -> Node v a
node2 a b    =   Node2 (measure a `mappend` measure b) a b

node3        ::  (Measured v a) => a -> a -> a -> Node v a
node3 a b c  =   Node3 (measure a `mappend` measure b `mappend` measure c) a b c

instance (Monoid v) => Measured v (Node v a) where
    measure (Node2 v _ _)    =  v
    measure (Node3 v _ _ _)  =  v


{-@ nodeToDigit :: n:Node v a -> {d:Digit a | nodeSize n == digitSize d}  @-} 
nodeToDigit :: Node v a -> Digit a
nodeToDigit (Node2 _ a b) = Two a b
nodeToDigit (Node3 _ a b c) = Three a b c

-- | A representation of a sequence of values of type @a@, allowing
-- access to the ends in constant time, and append and split in time
-- logarithmic in the size of the smaller piece.
--
-- The collection is also parameterized by a measure type @v@, which
-- is used to specify a position in the sequence for the 'split' operation.
-- The types of the operations enforce the constraint @'Measured' v a@,
-- which also implies that the type @v@ is determined by @a@.
--
-- A variety of abstract data types can be implemented by using different
-- element types and measurements.

{-@ data FingerTree v a = 
    Empty
    | Single a
    | Deep {
        _v :: v, 
        left :: (Digit a),
        mid :: (FingerTree v (Node v a)),
        right :: (Digit a)
    }
@-}
data FingerTree v a
    = Empty
    | Single a
    | Deep v (Digit a) (FingerTree v (Node v a)) (Digit a)
    deriving Show

-- {-@ measure fingerTreeSize @-}
-- fingerTreeSize :: FingerTree v a -> Int
-- fingerTreeSize Empty = 0
-- fingerTreeSize Single{} = 1
-- fingerTreeSize (Deep _ l m r) = length l + digitSize r + fingerTreeSize m


deep ::  (Measured v a) =>
     Digit a -> FingerTree v (Node v a) -> Digit a -> FingerTree v a
deep pr m sf =
    Deep ((measure pr `mappend` measure m) `mappend` measure sf) pr m sf

-- | /O(1)/. The cached measure of a tree.
instance (Measured v a) => Measured v (FingerTree v a) where
    measure Empty           =  mempty
    measure (Single x)      =  measure x
    measure (Deep v _ _ _)  =  v

-- | Elements from left to right.
instance Foldable (FingerTree v) where
    foldMap _ Empty = mempty
    foldMap f (Single x) = f x
    foldMap f (Deep _ pr m sf) =
        foldMap f pr `mappend` foldMap (foldMap f) m `mappend` foldMap f sf


-- | /O(1)/. The empty sequence.
empty :: Measured v a => FingerTree v a
empty = Empty

-- | /O(1)/. A singleton sequence.
singleton :: Measured v a => a -> FingerTree v a
singleton = Single

-- | /O(n)/. Create a sequence from a finite list of elements.
-- The opposite operation 'toList' is supplied by the 'Foldable' instance.
fromList :: (Measured v a) => [a] -> FingerTree v a
fromList = foldr (<|) Empty

-- | /O(1)/. Add an element to the left end of a sequence.
-- Mnemonic: a triangle with the single element at the pointy end.
(<|) :: (Measured v a) => a -> FingerTree v a -> FingerTree v a
a <| Empty              =  Single a
a <| Single b           =  deep (One a) Empty (One b)
a <| Deep v (Four b c d e) m sf = m `seq`
    Deep (measure a `mappend` v) (Two a b) (node3 c d e <| m) sf
a <| Deep v pr m sf     =
    Deep (measure a `mappend` v) (consDigit a pr) m sf

consDigit :: a -> Digit a -> Digit a
consDigit a (One b) = Two a b
consDigit a (Two b c) = Three a b c
consDigit a (Three b c d) = Four a b c d
consDigit _ (Four _ _ _ _) = illegal_argument "consDigit"

-- | /O(1)/. Add an element to the right end of a sequence.
-- Mnemonic: a triangle with the single element at the pointy end.
(|>) :: (Measured v a) => FingerTree v a -> a -> FingerTree v a
Empty |> a              =  Single a
Single a |> b           =  deep (One a) Empty (One b)
Deep v pr m (Four a b c d) |> e = m `seq`
    Deep (v `mappend` measure e) pr (m |> node3 a b c) (Two d e)
Deep v pr m sf |> x     =
    Deep (v `mappend` measure x) pr m (snocDigit sf x)

snocDigit :: Digit a -> a -> Digit a
snocDigit (One a) b = Two a b
snocDigit (Two a b) c = Three a b c
snocDigit (Three a b c) d = Four a b c d
snocDigit (Four _ _ _ _) _ = illegal_argument "snocDigit"

-- | /O(1)/. Is this the empty sequence?
null :: FingerTree v a -> Bool
null Empty = True
null _ = False

-- | /O(1)/. Analyse the left end of a sequence.
viewl :: (Measured v a) => FingerTree v a -> ViewL (FingerTree v) a
viewl Empty                     =  EmptyL
viewl (Single x)                =  x :< Empty
viewl (Deep _ (One x) m sf)     =  x :< rotL m sf
viewl (Deep _ pr m sf)          =  lheadDigit pr :< deep (ltailDigit pr) m sf

rotL :: (Measured v a) => FingerTree v (Node v a) -> Digit a -> FingerTree v a
rotL m sf      =   case viewl m of
    EmptyL  ->  digitToTree sf
    a :< m' ->  Deep (measure m `mappend` measure sf) (nodeToDigit a) m' sf

lheadDigit :: Digit a -> a
lheadDigit (One a) = a
lheadDigit (Two a _) = a
lheadDigit (Three a _ _) = a
lheadDigit (Four a _ _ _) = a

ltailDigit :: Digit a -> Digit a
ltailDigit (One _) = illegal_argument "ltailDigit"
ltailDigit (Two _ b) = One b
ltailDigit (Three _ b c) = Two b c
ltailDigit (Four _ b c d) = Three b c d

-- | /O(1)/. Analyse the right end of a sequence.
viewr :: (Measured v a) => FingerTree v a -> ViewR (FingerTree v) a
viewr Empty                     =  EmptyR
viewr (Single x)                =  Empty :> x
viewr (Deep _ pr m (One x))     =  rotR pr m :> x
viewr (Deep _ pr m sf)          =  deep pr m (rtailDigit sf) :> rheadDigit sf

rotR :: (Measured v a) => Digit a -> FingerTree v (Node v a) -> FingerTree v a
rotR pr m = case viewr m of
    EmptyR  ->  digitToTree pr
    m' :> a ->  Deep (measure pr `mappend` measure m) pr m' (nodeToDigit a)

rheadDigit :: Digit a -> a
rheadDigit (One a) = a
rheadDigit (Two _ b) = b
rheadDigit (Three _ _ c) = c
rheadDigit (Four _ _ _ d) = d

rtailDigit :: Digit a -> Digit a
rtailDigit (One _) = illegal_argument "rtailDigit"
rtailDigit (Two a _) = One a
rtailDigit (Three a b _) = Two a b
rtailDigit (Four a b c _) = Three a b c

digitToTree :: (Measured v a) => Digit a -> FingerTree v a
digitToTree (One a) = Single a
digitToTree (Two a b) = deep (One a) Empty (One b)
digitToTree (Three a b c) = deep (Two a b) Empty (One c)
digitToTree (Four a b c d) = deep (Two a b) Empty (Two c d)

(><) :: (Measured v a) => FingerTree v a -> FingerTree v a -> FingerTree v a
--(><) =  appendTree0
(><) = undefined

-- appendTree0 :: (Measured v a) => FingerTree v a -> FingerTree v a -> FingerTree v a
-- appendTree0 Empty xs =
--     xs
-- appendTree0 xs Empty =
--     xs
-- appendTree0 (Single x) xs =
--     x <| xs
-- appendTree0 xs (Single x) =
--     xs |> x
-- appendTree0 (Deep _ pr1 m1 sf1) (Deep _ pr2 m2 sf2) =
--     deep pr1 (addDigits0 m1 sf1 pr2 m2) sf2

-- addDigits0 :: (Measured v a) => FingerTree v (Node v a) -> Digit a -> Digit a -> FingerTree v (Node v a) -> FingerTree v (Node v a)
-- addDigits0 m1 (One a) (One b) m2 =
--     appendTree1 m1 (node2 a b) m2
-- addDigits0 m1 (One a) (Two b c) m2 =
--     appendTree1 m1 (node3 a b c) m2
-- addDigits0 m1 (One a) (Three b c d) m2 =
--     appendTree2 m1 (node2 a b) (node2 c d) m2
-- addDigits0 m1 (One a) (Four b c d e) m2 =
--     appendTree2 m1 (node3 a b c) (node2 d e) m2
-- addDigits0 m1 (Two a b) (One c) m2 =
--     appendTree1 m1 (node3 a b c) m2
-- addDigits0 m1 (Two a b) (Two c d) m2 =
--     appendTree2 m1 (node2 a b) (node2 c d) m2
-- addDigits0 m1 (Two a b) (Three c d e) m2 =
--     appendTree2 m1 (node3 a b c) (node2 d e) m2
-- addDigits0 m1 (Two a b) (Four c d e f) m2 =
--     appendTree2 m1 (node3 a b c) (node3 d e f) m2
-- addDigits0 m1 (Three a b c) (One d) m2 =
--     appendTree2 m1 (node2 a b) (node2 c d) m2
-- addDigits0 m1 (Three a b c) (Two d e) m2 =
--     appendTree2 m1 (node3 a b c) (node2 d e) m2
-- addDigits0 m1 (Three a b c) (Three d e f) m2 =
--     appendTree2 m1 (node3 a b c) (node3 d e f) m2
-- addDigits0 m1 (Three a b c) (Four d e f g) m2 =
--     appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
-- addDigits0 m1 (Four a b c d) (One e) m2 =
--     appendTree2 m1 (node3 a b c) (node2 d e) m2
-- addDigits0 m1 (Four a b c d) (Two e f) m2 =
--     appendTree2 m1 (node3 a b c) (node3 d e f) m2
-- addDigits0 m1 (Four a b c d) (Three e f g) m2 =
--     appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
-- addDigits0 m1 (Four a b c d) (Four e f g h) m2 =
--     appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2

-- appendTree1 :: (Measured v a) => FingerTree v a -> a -> FingerTree v a -> FingerTree v a
-- appendTree1 Empty a xs =
--     a <| xs
-- appendTree1 xs a Empty =
--     xs |> a
-- appendTree1 (Single x) a xs =
--     x <| a <| xs
-- appendTree1 xs a (Single x) =
--     xs |> a |> x
-- appendTree1 (Deep _ pr1 m1 sf1) a (Deep _ pr2 m2 sf2) =
--     deep pr1 (addDigits1 m1 sf1 a pr2 m2) sf2

-- addDigits1 :: (Measured v a) => FingerTree v (Node v a) -> Digit a -> a -> Digit a -> FingerTree v (Node v a) -> FingerTree v (Node v a)
-- addDigits1 m1 (One a) b (One c) m2 =
--     appendTree1 m1 (node3 a b c) m2
-- addDigits1 m1 (One a) b (Two c d) m2 =
--     appendTree2 m1 (node2 a b) (node2 c d) m2
-- addDigits1 m1 (One a) b (Three c d e) m2 =
--     appendTree2 m1 (node3 a b c) (node2 d e) m2
-- addDigits1 m1 (One a) b (Four c d e f) m2 =
--     appendTree2 m1 (node3 a b c) (node3 d e f) m2
-- addDigits1 m1 (Two a b) c (One d) m2 =
--     appendTree2 m1 (node2 a b) (node2 c d) m2
-- addDigits1 m1 (Two a b) c (Two d e) m2 =
--     appendTree2 m1 (node3 a b c) (node2 d e) m2
-- addDigits1 m1 (Two a b) c (Three d e f) m2 =
--     appendTree2 m1 (node3 a b c) (node3 d e f) m2
-- addDigits1 m1 (Two a b) c (Four d e f g) m2 =
--     appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
-- addDigits1 m1 (Three a b c) d (One e) m2 =
--     appendTree2 m1 (node3 a b c) (node2 d e) m2
-- addDigits1 m1 (Three a b c) d (Two e f) m2 =
--     appendTree2 m1 (node3 a b c) (node3 d e f) m2
-- addDigits1 m1 (Three a b c) d (Three e f g) m2 =
--     appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
-- addDigits1 m1 (Three a b c) d (Four e f g h) m2 =
--     appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
-- addDigits1 m1 (Four a b c d) e (One f) m2 =
--     appendTree2 m1 (node3 a b c) (node3 d e f) m2
-- addDigits1 m1 (Four a b c d) e (Two f g) m2 =
--     appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
-- addDigits1 m1 (Four a b c d) e (Three f g h) m2 =
--     appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
-- addDigits1 m1 (Four a b c d) e (Four f g h i) m2 =
--     appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2

-- appendTree2 :: (Measured v a) => FingerTree v a -> a -> a -> FingerTree v a -> FingerTree v a
-- appendTree2 Empty a b xs =
--     a <| b <| xs
-- appendTree2 xs a b Empty =
--     xs |> a |> b
-- appendTree2 (Single x) a b xs =
--     x <| a <| b <| xs
-- appendTree2 xs a b (Single x) =
--     xs |> a |> b |> x
-- appendTree2 (Deep _ pr1 m1 sf1) a b (Deep _ pr2 m2 sf2) =
--     deep pr1 (addDigits2 m1 sf1 a b pr2 m2) sf2

-- addDigits2 :: (Measured v a) => FingerTree v (Node v a) -> Digit a -> a -> a -> Digit a -> FingerTree v (Node v a) -> FingerTree v (Node v a)
-- addDigits2 m1 (One a) b c (One d) m2 =
--     appendTree2 m1 (node2 a b) (node2 c d) m2
-- addDigits2 m1 (One a) b c (Two d e) m2 =
--     appendTree2 m1 (node3 a b c) (node2 d e) m2
-- addDigits2 m1 (One a) b c (Three d e f) m2 =
--     appendTree2 m1 (node3 a b c) (node3 d e f) m2
-- addDigits2 m1 (One a) b c (Four d e f g) m2 =
--     appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
-- addDigits2 m1 (Two a b) c d (One e) m2 =
--     appendTree2 m1 (node3 a b c) (node2 d e) m2
-- addDigits2 m1 (Two a b) c d (Two e f) m2 =
--     appendTree2 m1 (node3 a b c) (node3 d e f) m2
-- addDigits2 m1 (Two a b) c d (Three e f g) m2 =
--     appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
-- addDigits2 m1 (Two a b) c d (Four e f g h) m2 =
--     appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
-- addDigits2 m1 (Three a b c) d e (One f) m2 =
--     appendTree2 m1 (node3 a b c) (node3 d e f) m2
-- addDigits2 m1 (Three a b c) d e (Two f g) m2 =
--     appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
-- addDigits2 m1 (Three a b c) d e (Three f g h) m2 =
--     appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
-- addDigits2 m1 (Three a b c) d e (Four f g h i) m2 =
--     appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
-- addDigits2 m1 (Four a b c d) e f (One g) m2 =
--     appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
-- addDigits2 m1 (Four a b c d) e f (Two g h) m2 =
--     appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
-- addDigits2 m1 (Four a b c d) e f (Three g h i) m2 =
--     appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
-- addDigits2 m1 (Four a b c d) e f (Four g h i j) m2 =
--     appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2

-- appendTree3 :: (Measured v a) => FingerTree v a -> a -> a -> a -> FingerTree v a -> FingerTree v a
-- appendTree3 Empty a b c xs =
--     a <| b <| c <| xs
-- appendTree3 xs a b c Empty =
--     xs |> a |> b |> c
-- appendTree3 (Single x) a b c xs =
--     x <| a <| b <| c <| xs
-- appendTree3 xs a b c (Single x) =
--     xs |> a |> b |> c |> x
-- appendTree3 (Deep _ pr1 m1 sf1) a b c (Deep _ pr2 m2 sf2) =
--     deep pr1 (addDigits3 m1 sf1 a b c pr2 m2) sf2

-- addDigits3 :: (Measured v a) => FingerTree v (Node v a) -> Digit a -> a -> a -> a -> Digit a -> FingerTree v (Node v a) -> FingerTree v (Node v a)
-- addDigits3 m1 (One a) b c d (One e) m2 =
--     appendTree2 m1 (node3 a b c) (node2 d e) m2
-- addDigits3 m1 (One a) b c d (Two e f) m2 =
--     appendTree2 m1 (node3 a b c) (node3 d e f) m2
-- addDigits3 m1 (One a) b c d (Three e f g) m2 =
--     appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
-- addDigits3 m1 (One a) b c d (Four e f g h) m2 =
--     appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
-- addDigits3 m1 (Two a b) c d e (One f) m2 =
--     appendTree2 m1 (node3 a b c) (node3 d e f) m2
-- addDigits3 m1 (Two a b) c d e (Two f g) m2 =
--     appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
-- addDigits3 m1 (Two a b) c d e (Three f g h) m2 =
--     appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
-- addDigits3 m1 (Two a b) c d e (Four f g h i) m2 =
--     appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
-- addDigits3 m1 (Three a b c) d e f (One g) m2 =
--     appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
-- addDigits3 m1 (Three a b c) d e f (Two g h) m2 =
--     appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
-- addDigits3 m1 (Three a b c) d e f (Three g h i) m2 =
--     appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
-- addDigits3 m1 (Three a b c) d e f (Four g h i j) m2 =
--     appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
-- addDigits3 m1 (Four a b c d) e f g (One h) m2 =
--     appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
-- addDigits3 m1 (Four a b c d) e f g (Two h i) m2 =
--     appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
-- addDigits3 m1 (Four a b c d) e f g (Three h i j) m2 =
--     appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
-- addDigits3 m1 (Four a b c d) e f g (Four h i j k) m2 =
--     appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2

-- appendTree4 :: (Measured v a) => FingerTree v a -> a -> a -> a -> a -> FingerTree v a -> FingerTree v a
-- appendTree4 Empty a b c d xs =
--     a <| b <| c <| d <| xs
-- appendTree4 xs a b c d Empty =
--     xs |> a |> b |> c |> d
-- appendTree4 (Single x) a b c d xs =
--     x <| a <| b <| c <| d <| xs
-- appendTree4 xs a b c d (Single x) =
--     xs |> a |> b |> c |> d |> x
-- appendTree4 (Deep _ pr1 m1 sf1) a b c d (Deep _ pr2 m2 sf2) =
--     deep pr1 (addDigits4 m1 sf1 a b c d pr2 m2) sf2

-- addDigits4 :: (Measured v a) => FingerTree v (Node v a) -> Digit a -> a -> a -> a -> a -> Digit a -> FingerTree v (Node v a) -> FingerTree v (Node v a)
-- addDigits4 m1 (One a) b c d e (One f) m2 =
--     appendTree2 m1 (node3 a b c) (node3 d e f) m2
-- addDigits4 m1 (One a) b c d e (Two f g) m2 =
--     appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
-- addDigits4 m1 (One a) b c d e (Three f g h) m2 =
--     appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
-- addDigits4 m1 (One a) b c d e (Four f g h i) m2 =
--     appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
-- addDigits4 m1 (Two a b) c d e f (One g) m2 =
--     appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
-- addDigits4 m1 (Two a b) c d e f (Two g h) m2 =
--     appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
-- addDigits4 m1 (Two a b) c d e f (Three g h i) m2 =
--     appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
-- addDigits4 m1 (Two a b) c d e f (Four g h i j) m2 =
--     appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
-- addDigits4 m1 (Three a b c) d e f g (One h) m2 =
--     appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
-- addDigits4 m1 (Three a b c) d e f g (Two h i) m2 =
--     appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
-- addDigits4 m1 (Three a b c) d e f g (Three h i j) m2 =
--     appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
-- addDigits4 m1 (Three a b c) d e f g (Four h i j k) m2 =
--     appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
-- addDigits4 m1 (Four a b c d) e f g h (One i) m2 =
--     appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
-- addDigits4 m1 (Four a b c d) e f g h (Two i j) m2 =
--     appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
-- addDigits4 m1 (Four a b c d) e f g h (Three i j k) m2 =
--     appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
-- addDigits4 m1 (Four a b c d) e f g h (Four i j k l) m2 =
--     appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node3 j k l) m2



illegal_argument = error



ft1 :: Measured v a => FingerTree v a
ft1 = fromList ([1..10] :: [Int])

main :: IO ()
main = do
    print "test"
    print ft1