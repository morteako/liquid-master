
data Pair a = PNil | Cons a (Pair a) | Comp (Pair a) (Pair a)

Eq a => Eq (Pair a) where
    PNil == PNil = True
    (Cons a pa) == (Cons b pb) = a == b && pa == pb
    (Comp pa pb) == (Comp qa qb) = pa == qa && pb == qb
    _ == _ = False

psize : Pair a -> Int
psize PNil = 0
psize (Cons a p) = 1 + psize p
psize (Comp p p') = 1 + psize p + psize p'


pmap : (a->b) -> Pair a -> Pair b
pmap f PNil = PNil
pmap f (Cons a p) = Cons (f a) (pmap f p)
pmap f (Comp p p') = Comp (pmap f p) (pmap f p')

implementation Functor Pair where
    map = pmap

pmapId : (p : Pair a) -> (map Prelude.Basics.id p = p)
pmapId PNil = Refl
pmapId (Cons x y) = rewrite pmapId y in Refl
pmapId (Comp x y) =
        rewrite pmapId x in rewrite pmapId y in Refl



pmapComp : (p : Pair a) -> (f: b -> c) -> (g : a -> b) -> (map (f . g) p = map f (map g p))
pmapComp PNil f g = Refl
pmapComp (Cons x y) f g = rewrite pmapComp y f g in Refl
pmapComp (Comp x y) f g = rewrite pmapComp x f g in rewrite pmapComp y f g in Refl




appendPair : Pair a -> Pair a -> Pair a
appendPair PNil p = p
appendPair (Cons a p) p2 = Cons a (appendPair p p2)
appendPair (Comp p1 p2) p3 = Comp (appendPair p1 p3) p2


concatPair : Pair (Pair a) -> Pair a
concatPair PNil = PNil
concatPair (Cons p1 p2) = appendPair p1 (concatPair p2)
concatPair (Comp p1 p2) = Comp (concatPair p1) (concatPair p2)

pairFlatMap : (a -> Pair b) -> Pair a -> Pair b
pairFlatMap f p = concatPair (map f p)


Applicative Pair where
    pure x = Cons x PNil
    fs <*> as = pairFlatMap (\f => pairFlatMap (pure . f) as) fs

Monad Pair where
    (>>=) = flip pairFlatMap

preturn : a -> Pair a
preturn = pure



--PROOFS



appendPairRightId : (p : Pair a) -> appendPair p PNil = p
appendPairRightId PNil = Refl
appendPairRightId (Cons x y) = rewrite appendPairRightId y in Refl
appendPairRightId (Comp a b) = rewrite appendPairRightId a in Refl


-- law 1
mLeftId : (x : a) -> (f : a -> Pair b) -> ((preturn x >>= f) = f x)
mLeftId x f = appendPairRightId (f x)


--Should be able to generalize this stuff?
consLemma1 : {p:Pair x} -> {a: x} -> {b:x} -> a = b -> Cons a p = Cons b p
consLemma1 eqab = rewrite eqab in Refl

consLemma2 : {a:_} -> p1 = p2 -> Cons a p1 = Cons a p2
consLemma2 prf = rewrite prf in Refl

consLemma : {p1:Pair x} -> {a:x} -> {b:x} -> a = b -> p1 = p2 -> Cons a p1 = Cons b p2
consLemma {p1} {a} {b} prfAB prfP =
    let en = consLemma1 {p=p1} {a} {b} prfAB
        to = consLemma2 {a=b} prfP
    in
        trans en to

compLemma1 : {p:Pair x} ->  {a:Pair x} -> {b:Pair x} -> a = b -> Comp a p = Comp b p
compLemma1 eqab = rewrite eqab in Refl

compLemma2 : {p:_} -> p1 = p2 -> Comp p p1 = Comp p p2
compLemma2 prf = rewrite prf in Refl

compLemma : {p1:Pair x} -> {p2:Pair x} -> {p3:Pair x} -> p1 = p2 -> p3 = p4 -> Comp p1 p3 = Comp p2 p4
compLemma {p1} {p2} {p3} prfAB prfP =
    let en = compLemma1 {p=p3} {a=p1} {b=p2} prfAB
        to = compLemma2 {p=p2} prfP
    in
        trans en to


appLemma : appendPair ((\meth => Cons meth PNil) a1) p = Cons a1 p
appLemma = Refl

--law 2
mRightId : (ma : Pair a) -> (ma >>= (\meth => Cons meth PNil) = ma)
mRightId PNil = Refl
mRightId (Cons a p) = let   mp = mRightId p
                            cmp = consLemma2 mp
                        in trans appLemma cmp
mRightId (Comp a b) = let ma = mRightId a
                          mb = mRightId b
                    in compLemma ma mb


appendPairAssoc : 
    {p1 : Pair a} ->
    {p2 : Pair a} ->
    {p3 : Pair a} ->
    appendPair p1 (appendPair p2 p3) = appendPair (appendPair p1 p2) p3
appendPairAssoc {p1=PNil} {p2} {p3} = 
    Refl
appendPairAssoc {p1 = Cons x y} {p2} {p3} = 
        rewrite appendPairAssoc {p1=y} {p2} {p3}  in Refl
appendPairAssoc {p1 = Comp x y} {p2} {p3} = 
        rewrite appendPairAssoc {p1=x} {p2} {p3} in Refl
    

appendPairDistOverConcat : 
    {p1 : Pair (Pair a)} -> 
    {p2 : Pair (Pair a)} ->
    concatPair (appendPair p1 p2) = appendPair (concatPair p1) (concatPair p2)
appendPairDistOverConcat {p1 = PNil} {p2 = p2} = Refl
appendPairDistOverConcat {p1 = (Cons x y)} {p2 = p2} = 
    let 
        ay = appendPairDistOverConcat {p1 = y} {p2}
    in trans (cong ay) appendPairAssoc
appendPairDistOverConcat {p1 = (Comp x y)} {p2 = p2} = 
    compLemma1 (appendPairDistOverConcat {p1=x} {p2})


distPmap : {p1 : Pair a} -> {p2 : Pair a} -> {f : a -> b} -> map f (appendPair p1 p2) = appendPair (map f p1) (map f p2)
distPmap {p1 = PNil} {p2 = p2} {f} = Refl
distPmap {p1 = (Cons x y)} {p2 = p2} {f} =
        cong (distPmap {p1=y} {p2})
distPmap {p1 = (Comp x y)} {p2 = p2} {f} = 
    let
        dx = distPmap {p1=x} {p2} {f}
        dy = distPmap {p1=y} {p2} {f}
    in
        compLemma1 {p=pmap f y} dx


appCongLemma : (a = b) -> appendPair p a = appendPair p b
appCongLemma prf = rewrite prf in Refl

--law 3
mAssoc : 
    (ma : Pair a) -> 
    (f : a -> Pair b) -> 
    (g : b -> Pair c) -> 
    (ma >>= f >>= g) = ma >>= (\x => f x >>= g)
mAssoc PNil f g= Refl
mAssoc (Cons x y) f g=
        let
            my = mAssoc y f g 
            distPmapOnY = distPmap {f=g} {p1 = f x} {p2 = concatPair (pmap f y)}
           
            distAppend = appendPairDistOverConcat 
                    {p1=(pmap g (f x))} 
                    {p2= (pmap g (concatPair (pmap f y)))}                  
        in (cong distPmapOnY `trans` distAppend) `trans` (appCongLemma my)   
mAssoc (Comp x y) f g= 
    let
        mx = mAssoc x f g
        my = mAssoc y f g
    in 
        compLemma mx my



