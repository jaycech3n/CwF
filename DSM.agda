{-# OPTIONS --without-K #-}

{--- Decidable subsets of morphisms in well presented semicategories ---}

open import SuitableSemicategory

module DSM {ℓ}
  {Ob : Type ℓ}
  ⦃ C : LocallyFiniteSemicategoryOn Ob ⦄
  (_≟-Ob_ : has-dec-eq Ob) where

open LocallyFiniteSemicategoryOn C

-- Important fact
Ob-is-set : is-set Ob
Ob-is-set = dec-eq-is-set _≟-Ob_


{- Decidable subsets of morphisms -}

DSM : Type ℓ
DSM = {x y : Ob} → Hom x y → Bool

-- Membership
_∈ₘ_ : {x y : Ob} → Hom x y → DSM → Type₀
f ∈ₘ σ = is-true (σ f)

-- Subset
_⊆ₘ_ : DSM → DSM → Type ℓ
σ ⊆ₘ σ' = ∀ {x} {y} {f : Hom x y} → (f ∈ₘ σ) → (f ∈ₘ σ')

-- Operations on DSMs

Ø : DSM
Ø _ = false

_∩_ : DSM → DSM → DSM
(σ ∩ σ') f = σ f and σ' f

add-arrow : {u v : Ob} → Hom u v → DSM → DSM
add-arrow {u} {v} g σ {x} {y} f
 with x ≟-Ob u | y ≟-Ob v
... | inl idp  | inl idp = σ f or to-Bool (f ≟-Hom g)
... | inl idp  | inr _   = σ f
... | inr _    | _       = σ f

add-arrow-⊆ : ∀ {σ : DSM} {u v} {g : Hom u v}
              → σ ⊆ₘ add-arrow g σ
add-arrow-⊆ {σ} {u = u} {v} {x = x} {y} m
 with x ≟-Ob u | y ≟-Ob v
... | inl idp  | inl idp rewrite ⌞ m ⌟ = _
... | inl idp  | inr _   = m
... | inr _    | _       = m

add-arrow-new : ∀ {x y} (f : Hom x y) {σ : DSM}
                → f ∈ₘ add-arrow f σ
add-arrow-new {x} {y} f {σ} with x ≟-Ob x
... | inl p rewrite is-set-UIP Ob-is-set p
            with y ≟-Ob y
...            | inl q rewrite is-set-UIP Ob-is-set q
                             | =-refl-bool _≟-Hom_ f
                             | or-sym (σ f) true
                       = _
...            | inr ¬q = ⊥-rec (¬q idp)
add-arrow-new {x} {y} f {σ}
    | inr ¬p = ⊥-rec (¬p idp)

{- Probably need this at some point:
add-arrow-compl : ∀ {u v} (g : Hom u v) {σ : DSM}
                    {x y} (f : Hom x y)
                  → ¬ (f ∈ₘ σ)
                  → {!¬ (f == g)!}
                  → ¬ f ∈ₘ add-arrow f σ
-}
