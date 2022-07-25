{-# OPTIONS --without-K #-}

open import SuitableSemicategories

{--- Decidable subsets of morphisms in locally finite semicats ---}

module DSM {ℓ}
  { Ob : Type ℓ }
  ⦃ C : LocallyFiniteSemicategoryOn Ob ⦄
  ( _≟-Ob_ : has-dec-eq Ob ) where

open LocallyFiniteSemicategoryOn C


-- Important
Ob-is-set : is-set Ob
Ob-is-set = dec-eq-is-set _≟-Ob_


{- Decidable subsets of morphisms -}

DSM : Type ℓ
DSM = (x y : Ob) → Hom x y → Bool

⟦_⟧ : DSM → {x y : Ob} → Hom x y → Bool
⟦ σ ⟧ {x} {y} = σ x y

_∈ₘ_ : {x y : Ob} → Hom x y → DSM → Type₀
f ∈ₘ σ = is-true (⟦ σ ⟧ f)

_⊆ₘ_ : DSM → DSM → Type ℓ
σ ⊆ₘ σ' = ∀ {x} {y} {f : Hom x y} → (f ∈ₘ σ) → (f ∈ₘ σ')

Ø : DSM
Ø _ _ _ = false

_∩_ : DSM → DSM → DSM
(σ ∩ σ') _ _ f = ⟦ σ ⟧ f and ⟦ σ' ⟧ f

_∪_ : DSM → DSM → DSM
(σ ∪ σ') _ _ f = ⟦ σ ⟧ f or ⟦ σ' ⟧ f

DSM= : {σ σ' : DSM}
       → (∀ x y → (f : Hom x y) → σ x y f == σ' x y f)
       → σ == σ'
DSM= = λ=₃


{- Decidable subsets of hom-sets

Restricted form of DSM, fixing the source and target.
-}

DSHom : ∀ x y → Type ℓ
DSHom x y = Hom x y → Bool

DSM-of : ∀ {x y} → DSHom x y → DSM
DSM-of {x} {y} σ u v g
 with u ≟-Ob x | v ≟-Ob y
... | inr _    | _       = false
... | inl _    | inr _   = false
... | inl idp  | inl idp = σ g

module _ where
  -- (size-aux {x} {y} σ t _) is the number of arrows f: x → y, up to and
  -- including [t], in σ.
  size-aux : ∀ {x y} → DSHom x y
             → (t : ℕ) → t < Hom-size x y
             → Σ[ n ∈ ℕ ] n ≤ 1+ t
  size-aux {x} {y} σ O u =
    Bool-rec (1 , ≤-ap-S lteE) (O , O≤ _) (σ [0])
    where [0] = Hom[ x , y ]# (O , u)
  size-aux {x} {y} σ (1+ t) u =
    Bool-rec (1+ prev-size , ≤-ap-S prev-size-cond)
             (prev-size , ≤-trans prev-size-cond lteS)
             (σ [1+t])
    where
      [1+t] = Hom[ x , y ]# (1+ t , u)
      rec = size-aux σ t (<-trans ltS u)
      prev-size = fst rec
      prev-size-cond = snd rec

  size : ∀ {x y} → DSHom x y → Σ[ n ∈ ℕ ] n ≤ Hom-size x y
  size {x} {y} σ with Hom-size x y | inspect (Hom-size x) y
  ... | O    | _ = O , lteE
  ... | S n  | with-eq p = size-aux σ n (tr (n <_) (! p) ltS)
