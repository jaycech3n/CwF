{-# OPTIONS --without-K #-}

open import SuitableSemicategories

module SieveIntersection ⦃ I : SuitableSemicategory ⦄ where
open SuitableSemicategory I

open import Sieves public


factors-cumul : ∀ {i h m} → (t : Fin (Hom-size i h)) → Hom i m → DSHom m h
factors-cumul t f g = to-Bool (idx-of (g ◦ f) ≤?-Fin t)

[_,_,_]∩[_,_] : (i h t : ℕ) (m : ℕ) (f : Hom i m) → is-shape i h t → Shape
[ i , h , 1+ t ]∩[ m , f ] iS
 with Hom[ i , h ]# (t , S≤→< (tcond iS)) factors-through? f
... | inr no = [ i , h , t ]∩[ m , f ] (shape-from-next-t iS)
... | inl (w , _) = (m , h , new-width) ,
                      shape-conds (inr (Hom-inverse m h w)) width-cond
      where
        incr-width : Σ[ t ∈ ℕ ] t ≤ Hom-size m h
        incr-width = size (factors-cumul (t , S≤→< (tcond iS)) f)

        new-width = fst incr-width
        width-cond = snd incr-width
[ i , 1+ h , O ]∩[ m , f ] iS = [ i , h , Hom-size i h ]∩[ m , f ]
                                  (full-shape i h (≤-trans lteS (hcond iS)))
[ i ,   O  , O ]∩[ m , f ] iS = (m , O , O) , empty-shape m
