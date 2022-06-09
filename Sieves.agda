{-# OPTIONS --without-K #-}

open import SuitableSemicategory

module Sieves {ℓ}
  {Ob : Type ℓ}
  ⦃ C : LocallyFiniteSemicategoryOn Ob ⦄
  (_≟-Ob_ : has-dec-eq Ob) where

open LocallyFiniteSemicategoryOn C

open import DSM _≟-Ob_


Ob-is-set : is-set Ob
Ob-is-set = dec-eq-is-set _≟-Ob_


{- Principal sieves -}

⦅_⦆ : {x y : Ob} → Hom x y → DSM
⦅_⦆ {x} {y} f {u} {v} g =
  if (u ≟-Ob x)
     (λ{ idp → if (g factors-through? f) (λ yes → true) (λ no → false) })
     (λ no → false)

abstract
  ⦅_⦆-correct : ∀ {x y z : Ob} (f : Hom x y)
                → (g : Hom x z)
                → ⦅ f ⦆ g == to-Bool (g factors-through? f)
  ⦅_⦆-correct {x} {y} {z} f g with x ≟-Ob x
  ... | inl p rewrite is-set-UIP Ob-is-set p
              with g factors-through? f
  ...            | inl yes = idp
  ...            | inr no = idp
  ⦅_⦆-correct {x} {y} {z} f g
      | inr ¬p with g factors-through? f
  ...             | inl yes = ⊥-elim (¬p idp)
  ...             | inr no = idp

  -- Old alternate proof
  ⦅_⦆-correct' : ∀ {x y z : Ob} (f : Hom x y)
                 → (g : Hom x z)
                 → (g ∈ₘ ⦅ f ⦆) ≃ ∥ g factors-through f ∥
  ⦅_⦆-correct' {x} {y} {z} f g with x ≟-Ob x
  ... | inl p rewrite is-set-UIP Ob-is-set p
              with g factors-through? f
  ...            | inl w = prop-equiv (λ _ → ∣ w ∣) (λ _ → tt)
  ...            | inr ¬factor = prop-equiv ⊥-elim (Trunc-elim ¬factor)
  ⦅_⦆-correct' {x} {y} {z} f g
      | inr ¬p = prop-equiv ⊥-elim (Trunc-elim (λ _ → ¬p idp))


