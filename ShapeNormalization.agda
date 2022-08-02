{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import SuitableSemicategories

module ShapeNormalization ⦃ I : SuitableSemicategory ⦄ where
open SuitableSemicategory I

open import Shapes public


-- (norm↓ i h t) is the smallest member of the ~-equivalence class of (i, h, t).
norm↓ : ∀ i h t → is-shape i h t → Shape
norm↓ i h (1+ t) iS = (i , h , 1+ t) , iS
norm↓ i (1+ h) O iS = norm↓ i h (Hom-size i h) (shape-from-next-h iS)
norm↓ i O O iS = (i , O , O) , iS

-- (norm↑ i h t) is the largest member of the ~-equivalence class of (i, h, t).
norm↑ : ∀ i h {d : ℕ} {p : i ∸ h == d} → ∀ t → is-shape i h t → Shape
norm↑ i h {O} t iS = (i , h , t) , iS
norm↑ i h {1+ d} {p} t (shape-conds _ (inl _)) =
  norm↑ i (1+ h) {d} {∸-move-S-l i h p} O (shape-conds (<→S≤ (∸→< p)) (O≤ _))
norm↑ i h {1+ d} t iS@(shape-conds _ (inr _)) = (i , h , t) , iS

norm↑-unc : Shape → Shape
norm↑-unc ((i , h , t) , iS) = norm↑ i h {i ∸ h} {idp} t iS


{- Properties -}

private
  norm↑-rec-p = ∸-move-S-l

  norm↑-rec-shape-conds : ∀ {i h d} → i ∸ h == 1+ d → is-shape i (1+ h) O
  norm↑-rec-shape-conds p = shape-conds (<→S≤ (∸→< p)) (O≤ _)

norm↑-apex : ∀ i h {d} {p} t iS → apex (norm↑ i h {d} {p} t iS) == i
norm↑-apex i h {O} t iS = idp
norm↑-apex i h {1+ d} {p} t (shape-conds _ (inl _)) =
  norm↑-apex i (1+ h) {d} {norm↑-rec-p i h p} O (norm↑-rec-shape-conds p)
norm↑-apex i h {1+ d} t (shape-conds _ (inr _)) = idp

norm↑-unc-apex : ∀ (s : Shape) → apex (norm↑-unc s) == apex s
norm↑-unc-apex s = norm↑-apex i h {i ∸ h} {idp} t iS
  where
  i = apex s
  h = height s
  t = width s
  iS = snd s

norm↑-width : ∀ i h {d} {p} iS → width (norm↑ i h {d} {p} O iS) == O
norm↑-width i h {O} iS = idp
norm↑-width i h {1+ d} {p} (shape-conds _ (inl _)) =
  norm↑-width i (1+ h) {d} {norm↑-rec-p i h p} (norm↑-rec-shape-conds p)
norm↑-width i h {1+ d} (shape-conds _ (inr _)) = idp

module norm↑-height-lemmas where
  norm↑-height-monotone : ∀ i h {d} {p} t iS
    → h ≤ height (norm↑ i h {d} {p} t iS)
  norm↑-height-monotone i h {O} t iS = lteE
  norm↑-height-monotone i h {1+ d} {p} t (shape-conds _ (inl _)) =
    ≤-trans lteS
      (norm↑-height-monotone i (1+ h) {d} {norm↑-rec-p i h p} O
        (norm↑-rec-shape-conds p))
  norm↑-height-monotone i h {1+ d} t (shape-conds _ (inr _)) = lteE

  norm↑-height-Hom-size : ∀ i h {d} {p} t iS
    → height (norm↑ i h {d} {p} t iS) < i
    → O < Hom-size i (height (norm↑ i h {d} {p} t iS))
  norm↑-height-Hom-size i h {O} {p} t iS u = ⊥-rec (<-to-≱ u (∸→≤ p))
  norm↑-height-Hom-size i h {1+ d} {p} t (shape-conds _ (inl t=max)) u =
    norm↑-height-Hom-size i (1+ h) {d} {norm↑-rec-p i h p} O
      (norm↑-rec-shape-conds p) u
  norm↑-height-Hom-size i h {1+ d} t (shape-conds _ (inr t<max)) _ =
    ≤→<→< (O≤ _) t<max

  norm↑-height-nonempty : ∀ i h {d} {p} iS
    → O < Hom-size i h
    → height (norm↑ i h {d} {p} O iS) ≤ h
  norm↑-height-nonempty i h {O} iS u = lteE
  norm↑-height-nonempty i h {1+ d} (shape-conds _ (inl p)) u =
    ⊥-rec (¬-< (tr (O <_) (! p) u))
  norm↑-height-nonempty i h {1+ d} (shape-conds _ (inr _)) _ = lteE

  norm↑-height-max : ∀ i h {d} {p} t iS
    → ∀ m
    → h < m
    → O < Hom-size i m
    → height (norm↑ i h {d} {p} t iS) ≤ m
  norm↑-height-max i h {O} t iS m h<m _ = inr h<m
  norm↑-height-max i h {1+ d} {p} t (shape-conds _ (inl t=max)) m h<m O<H
   with <→S≤ h<m
  ... | inl idp = norm↑-height-nonempty i (1+ h) {d} (norm↑-rec-shape-conds p) O<H
  ... | inr Sh<m = norm↑-height-max i (1+ h) {d} {norm↑-rec-p i h p} O
                     (norm↑-rec-shape-conds p) m Sh<m O<H
  norm↑-height-max i h {1+ d} t (shape-conds _ (inr _)) m h<m _ = inr h<m

  norm-height-lem : ∀ i h {d} {p} t iS
    → ∀ m
    → h < m
    → m < height (norm↑ i h {d} {p} t iS)
    → Hom-size i m == O
  norm-height-lem i h {d} {p} t iS = {!!}
