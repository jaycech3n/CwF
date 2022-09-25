{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import SuitableSemicategories

module ShapeRestriction-scratch ⦃ I : SuitableSemicategory ⦄ where
open SuitableSemicategory I

open import ShapeNormalization public


[_,_,_]⊙[_,_] : (i h t : ℕ) (m : ℕ) (f : Hom i m) → is-shape i h t → Shape

-- Temporary
open import DSM _≟-ℕ_

factors-cumul : ∀ {i h m} → (t : Fin (Hom-size i h)) → Hom i m → DSHom m h
factors-cumul t f g = to-Bool (idx-of (g ◦ f) ≤?-Fin t)
-- end Temporary

[ i , h , 1+ t ]⊙[ m , f ] iS = {!!}
[ i , 1+ h , O ]⊙[ m , f ] iS =
  [ i , h , Hom-size i h ]⊙[ m , f ] (shape-from-next-h iS)
[ i , O , O ]⊙[ m , f ] iS = (m , O , O) , empty-shape m -- do you want to normalize up?

shape-lemma : ∀ i h t iS {d} {p} {m} f
  → m ≤ height (norm↑ i h t iS {d} {p})
  → [ i , h , t ]⊙[ m , f ] iS == norm↓ m m O (degen-shape m m lteE)

-- (i, h, t+1)
shape-lemma i h (1+ t) iS f u = {!!}

-- (i, h+1, 0)
shape-lemma i (1+ h) O iS {d} {p} {m} f u =
  shape-lemma i h (Hom-size i h) (shape-from-next-h iS)
    {1+ d} {≤→∸S→∸ (hcond iS) p} f
    (tr (m ≤_) (norm↑-height-eq' i h (shape-from-next-h iS) iS {d}) u)

-- (i, 0, 0)
shape-lemma i O O iS {O} f u rewrite ≤O→=O u = idp
shape-lemma i O O iS@(shape-conds _ (inl O=H)) {1+ d} {p} {m} f u =
  ! (norm↓-empty m m (degen-shape m m lteE) claim3)
  where
    claim1 : ∀ k → O < k → k < height (norm↑ i O O iS {p = p}) → Hom-size i k == O
    claim1 = norm↑-height-max-contra i O O iS {p = p}

    claim2 : ∀ k → k < height (norm↑ i O O iS {p = p}) → Hom-size i k == O
    claim2 O _ = ! O=H
    claim2 (1+ k) = claim1 (1+ k) (O<S k)

    claim3 : ∀ k → k < m → Hom-size m k == O
    claim3 k k<m = O≮→=O ↯↯
      where
      module _ (v : O < Hom-size m k) where
        w : Hom i k
        w = Hom[ m , k ]# (O , v) ◦ f

        c : O < Hom-size i k
        c = Hom[ i , k ]-inhab w

        k<h↑ : k < height (norm↑ i O O iS {p = p})
        k<h↑ = <→≤→< k<m u

        ↯↯ : ⊥
        ↯↯ = <-to-≠ c (! (claim2 k k<h↑))
shape-lemma i O O (shape-conds _ (inr _)) {1+ d} f u rewrite ≤O→=O u = idp
