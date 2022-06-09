{-# OPTIONS --without-K #-}

{--- Decidable subsets of morphisms in well presented semicategories ---}

open import SuitableSemicategory

module DSM {ℓ}
  {Ob : Type ℓ}
  ⦃ C : LocallyFiniteSemicategoryOn Ob ⦄
  (_≟-Ob_ : has-dec-eq Ob) where

open LocallyFiniteSemicategoryOn C

DSM : Type ℓ
DSM = {x y : Ob} → Hom x y → Bool

-- Operations on DSMs

Ø : DSM
Ø _ = false

add-arrow : {u v : Ob} → Hom u v → DSM → DSM
add-arrow {u} {v} g σ {x} {y} f =
  if (x ≟-Ob u)
     (λ{ idp →
         if (y ≟-Ob v)
            (λ{ idp → to-Bool (f ≟-Hom g)})
            (λ no → σ f) })
     (λ no → σ f)

_∩_ : DSM → DSM → DSM
(σ ∩ σ') f = σ f and σ' f

-- Membership
_∈ₘ_ : {x y : Ob} → Hom x y → DSM → Type₀
f ∈ₘ σ = is-true (σ f)
