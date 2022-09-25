{-# OPTIONS --without-K #-}

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
norm↑ : ∀ i h t → is-shape i h t → {d : ℕ} {p : i ∸ h == d} → Shape
norm↑ i h t iS {O} = (i , h , t) , iS
norm↑ i h _ (shape-conds _ (inl _)) {1+ d} {p} =
  norm↑ i (1+ h) O (shape-conds (<→S≤ (∸→< p)) (O≤ _)) {d} {∸-move-S-l i h p}
norm↑ i h t iS@(shape-conds _ (inr _)) {1+ d} = (i , h , t) , iS


module lemmas where
  abstract
    norm↓= : ∀ {i h t t'} {iS iS'}
      → t == t'
      → norm↓ i h t iS == norm↓ i h t' iS'
    norm↓= {i} {h} {1+ t} {.(1+ t)} {iS} {iS'} idp = Shape-idp
    norm↓= {i} {1+ h} {O} {.O} {iS} {iS'} idp = norm↓= {i} {h} {Hom-size i h} idp
    norm↓= {i} {O} {O} {.O} {iS} {iS'} idp = Shape-idp

    norm↓-empty : ∀ i h iS
      → (∀ k → k < h → Hom-size i k == O)
      → norm↓ i h O iS == (i , O , O) , empty-shape i
    norm↓-empty i O iS P = Shape-idp
    norm↓-empty i (1+ h) iS P = norm↓= (P h ltS) ∙ norm↓-empty i h iS' P'
      where
      iS' : is-shape i h O
      iS' = shape-conds (≤-trans lteS (hcond iS)) (O≤ _)

      P' : ∀ k → k < h → Hom-size i k == O
      P' k k<h = P k (ltSR k<h)

    norm↓-width>O : ∀ i h t iS iS' → O < t → norm↓ i h t iS == (i , h , t) , iS'
    norm↓-width>O i h (1+ t) iS iS' u = Shape-idp

    norm↓-min : ∀ i h iS j iS'
      → j < h
      → O < Hom-size i j
      → (∀ k → j < k → k < h → Hom-size i k == O)
      → norm↓ i h O iS == (i , j , Hom-size i j) , iS'
    norm↓-min i .(1+ j) iS j iS' ltS H P = norm↓-width>O i j (Hom-size i j) _ iS' H
    norm↓-min i (1+ j') iS j iS' (ltSR u) H P =
      norm↓= (P j' u ltS) ∙ norm↓-min i j' iS'' j iS' u H P'
      where
        iS'' : is-shape i j' O
        iS'' = shape-conds (≤-trans lteS (hcond iS)) (O≤ _)

        P' : (k : ℕ) → j < k → k < j' → Hom-size i k == O
        P' k v w = P k v (<-trans w ltS)

  private
    norm↑-rec-p = ∸-move-S-l

    norm↑-rec-shape-conds : ∀ {i h d} → i ∸ h == 1+ d → is-shape i (1+ h) O
    norm↑-rec-shape-conds p = shape-conds (<→S≤ (∸→< p)) (O≤ _)

  abstract
    norm↑= : ∀ i h t iS iS' {d} {p} {p'}
      → norm↑ i h t iS {d} {p} == norm↑ i h t iS' {d} {p'}
    norm↑= _ _ _ _ _ {O} = Shape-idp
    norm↑= i h _ (shape-conds _ (inl _)) (shape-conds _ (inl _)) {1+ d} {p} {p'} =
      norm↑= i (1+ h) O (norm↑-rec-shape-conds p) (norm↑-rec-shape-conds p') {d}
    norm↑= _ _ _ (shape-conds _ (inl idp)) (shape-conds _ (inr u)) {1+ d} =
      ⊥-rec (¬-< u)
    norm↑= _ _ _ (shape-conds _ (inr u)) (shape-conds _ (inl idp)) {1+ d} =
      ⊥-rec (¬-< u)
    norm↑= _ _ _ (shape-conds _ (inr _)) (shape-conds _ (inr _)) {1+ d} =
      Shape-idp

    norm↑-apex : ∀ i h t iS {d} {p} → apex (norm↑ i h t iS {d} {p}) == i
    norm↑-apex _ _ _ _ {O} = idp
    norm↑-apex i h _ (shape-conds _ (inl _)) {1+ d} {p} =
      norm↑-apex i (1+ h) O (norm↑-rec-shape-conds p) {d} {norm↑-rec-p i h p}
    norm↑-apex _ _ _ (shape-conds _ (inr _)) {1+ d} = idp

    norm↑-width : ∀ i h iS {d} {p} → width (norm↑ i h O iS {d} {p}) == O
    norm↑-width _ _ _ {O} = idp
    norm↑-width i h (shape-conds _ (inl _)) {1+ d} {p} =
      norm↑-width i (1+ h) (norm↑-rec-shape-conds p) {d} {norm↑-rec-p i h p}
    norm↑-width _ _ (shape-conds _ (inr _)) {1+ d} = idp

    norm↑-height-monotone : ∀ i h t iS {d} {p}
      → h ≤ height (norm↑ i h t iS {d} {p})
    norm↑-height-monotone _ _ _ _ {O} = lteE
    norm↑-height-monotone i h _ (shape-conds _ (inl _)) {1+ d} {p} =
      ≤-trans lteS
        (norm↑-height-monotone i (1+ h) O (norm↑-rec-shape-conds p)
          {d} {norm↑-rec-p i h p})
    norm↑-height-monotone _ _ _ (shape-conds _ (inr _)) {1+ d} = lteE

    norm↑-height-nonempty : ∀ i h iS {d} {p}
      → O < Hom-size i h
      → height (norm↑ i h O iS {d} {p}) ≤ h
    norm↑-height-nonempty _ _ _ {O} _ = lteE
    norm↑-height-nonempty _ _ (shape-conds _ (inl p)) {1+ d} u =
      ⊥-rec (¬-< (tr (O <_) (! p) u))
    norm↑-height-nonempty _ _ (shape-conds _ (inr _)) {1+ d} _ = lteE

    {-
    norm↑-height-Hom-size : ∀ i h t iS {d} {p}
      → height (norm↑ i h t iS {d} {p}) < i
      → O < Hom-size i (height (norm↑ i h t iS {d} {p}))
    norm↑-height-Hom-size _ _ _ _ {O} {p} u = ⊥-rec (<-to-≱ u (∸→≤ p))
    norm↑-height-Hom-size i h _ (shape-conds _ (inl _)) {1+ d} {p} u =
      norm↑-height-Hom-size i (1+ h) O (norm↑-rec-shape-conds p)
        {d} {norm↑-rec-p i h p} u
    norm↑-height-Hom-size _ _ _ (shape-conds _ (inr t<max)) {1+ d} _ =
      ≤→<→< (O≤ _) t<max
    -}

    norm↑-height-eq : ∀ i h t iS {d} {p} t' iS'
      → t < t'
      → t' < Hom-size i h
      → height (norm↑ i h t iS {d} {p}) == height (norm↑ i h t' iS' {d} {p})
    norm↑-height-eq _ _ _ _ {O} _ _ _ _ = idp
    norm↑-height-eq _ _ _ _ {1+ d}
      t' (shape-conds _ (inl idp)) _ t'<H = ⊥-rec (¬-< t'<H)
    norm↑-height-eq _ _ t (shape-conds _ (inl idp)) {1+ d}
      t' (shape-conds _ (inr x)) t<t' t'<H = ⊥-rec (¬-< (<-trans t<t' t'<H))
    norm↑-height-eq _ _ _ (shape-conds _ (inr _)) {1+ d}
      _ (shape-conds _ (inr _)) _ _ = idp

    norm↑-height-eq' : ∀ i h iS iS' {d} {p} {p'}
      → height (norm↑ i (1+ h) O iS' {d} {p'})
        == height (norm↑ i h (Hom-size i h) iS {1+ d} {p})
    norm↑-height-eq' _ _ (shape-conds _ (inl _)) _ {O} = idp
    norm↑-height-eq' _ _ (shape-conds _ (inr u)) _ {O} = ⊥-rec (¬-< u)
    norm↑-height-eq' i h (shape-conds _ (inl _)) iS' {1+ d} {p} =
      ap height (norm↑= i (1+ h) O iS' (norm↑-rec-shape-conds p) {1+ d})
    norm↑-height-eq' _ _ (shape-conds _ (inr u)) _ {1+ d} = ⊥-rec (¬-< u)

    norm↑-height-max : ∀ i h t iS {d} {p}
      → ∀ k
      → h < k
      → O < Hom-size i k
      → height (norm↑ i h t iS {d} {p}) ≤ k
    norm↑-height-max i h t iS {O} k h<k _ = inr h<k
    norm↑-height-max i h t (shape-conds _ (inl t=max)) {1+ d} {p} k h<k O<H
     with <→S≤ h<k
    ... | inl idp = norm↑-height-nonempty i (1+ h) (norm↑-rec-shape-conds p) {d} O<H
    ... | inr Sh<k = norm↑-height-max i (1+ h) O (norm↑-rec-shape-conds p)
                       {d} {norm↑-rec-p i h p} k Sh<k O<H
    norm↑-height-max i h t (shape-conds _ (inr _)) {1+ d} k h<k _ = inr h<k

    norm↑-height-max-contra : ∀ i h t iS {d} {p}
      → ∀ k
      → h < k
      → k < height (norm↑ i h t iS {d} {p})
      → Hom-size i k == O
    norm↑-height-max-contra i h t iS {d} {p} k h<k =
      ≤-contra (norm↑-height-max i h t iS {d} {p} k h<k)

open lemmas public
