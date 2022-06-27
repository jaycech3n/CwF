{-# OPTIONS --without-K #-}

open import SuitableSemicategories

module Sieves {ℓ}
  { Ob : Type ℓ }
  ⦃ C : LocallyFiniteSemicategoryOn Ob ⦄
  ( _≟-Ob_ : has-dec-eq Ob ) where

open import DSM _≟-Ob_ public

open LocallyFiniteSemicategoryOn C


{- Principal sieves -}

⦅_⦆ : {x y : Ob} → Hom x y → DSM
⦅_⦆ {u} {v} g {x} {y} f with x ≟-Ob u
... | inl idp = to-Bool (f factors-through? g)
... | inr _ = false

⦅_⦆-correct : ∀ {x y z : Ob} (g : Hom x y)
              → (f : Hom x z)
              → ⦅ g ⦆ f == to-Bool (f factors-through? g)
⦅_⦆-correct {x} {y} {z} g f with x ≟-Ob x
... | inl p rewrite is-set-UIP Ob-is-set p = idp
... | inr ¬p = ⊥-rec (¬p idp)
-- Can also reify the above into (f ∈ₘ ⦅ g ⦆) ≃ ∥ f factors-through g ∥
