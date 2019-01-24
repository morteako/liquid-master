{-@ lem_app_assoc :: fa:FingerTree a -> fb:FingerTree a -> fc:FingerTree a -> {app fa (app fb fc) == app (app fa fb) fc }  @-}
lem_app_assoc :: FingerTree a -> FingerTree a -> FingerTree a -> Proof
lem_app_assoc Empty fb fc = trivial
lem_app_assoc s@(Single a) fb fc
    =   app s (app fb fc) 
    === app3 s [] (app fb fc)
    === a <| (app fb fc)
    === app (a <| fb) fc
    === app (app3 s [] fb) fc
    === app (app s fb) fc
    *** QED




-- {-@ lazy lem_app_add_dist @-}
-- {-@ lem_app_add_dist :: x:a -> fa:FingerTree a -> fb:FingerTree a -> {x <| app fa fb == app (x <| fa) fb }  @-}
-- lem_app_add_dist :: a -> FingerTree a -> FingerTree a -> Proof
-- lem_app_add_dist x Empty fb = 1 === 2 *** QED
-- lem_app_add_dist x (Single y) fb = 1 === 2 *** QED
-- lem_app_add_dist x (Deep l m r) fb = 1 === 2 *** QED

