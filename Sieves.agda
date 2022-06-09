{-# OPTIONS --without-K #-}

open import SuitableSemicategory

module Sieves {ℓ} {Ob : Type ℓ} ⦃ C : LocallyFiniteSemicategoryOn Ob ⦄
  (_≟-Ob_ : has-dec-eq Ob)
  where

open LocallyFiniteSemicategoryOn C
open import DSM _≟-Ob_


Ob-is-set : is-set Ob
Ob-is-set = dec-eq-is-set _≟-Ob_


{- Principal sieves -}

⦅_⦆ : {x y : Ob} (f : Hom x y) → DSM
⦅_⦆ {x} {y} f (u , v , g) =
  if (u ≟-Ob x)
     (λ{ idp → if (g factors-through? f) (λ yes → true) (λ no → false) })
     (λ no → false)

abstract
  ⦅_⦆-correct : ∀ {x y z : Ob} (f : Hom x y)
                → (g : Hom x z)
                → is-true (⦅ f ⦆ (x , z , g)) ≃ ∥ g factors-through f ∥
  ⦅_⦆-correct {x} {y} {z} f g
   with x ≟-Ob x
  ... | inl p rewrite is-set-UIP Ob-is-set p
              with g factors-through? f
  ...            | inl (w , q) = equiv (λ _ → ∣ {!!} ∣) {!!} {!!} {!!}
  ...            | inr ¬factor = {!!}
  ⦅_⦆-correct {x} {y} {z} f g
      | inr ¬p = {!!}
