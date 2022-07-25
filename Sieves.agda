{-# OPTIONS --without-K #-}

open import SuitableSemicategories

module Sieves ⦃ I : SuitableSemicategory ⦄ where

open SuitableSemicategory I

open import DSM _≟-ℕ_ public
open import Shapes


{- Linear sieves -}

Sieve : (i h t : ℕ) (iS : is-shape i h t) → DSM
Sieve i h t iS x y f =
  if (x ≟-ℕ i)
     (λ{ idp → if (y ≤? h)
                  (λ{ (inl y=h) → to-Bool (ℕ-idx-of f <? t )
                    ; (inr y<h) → true })
                  (λ no → false) })
     (λ no → false)

Sieve-unc : Shape → DSM
Sieve-unc ((i , h , t) , iS) = Sieve i h t iS

Sieve-norm↓-ptwise : ∀ i h t iS x y f
                     → Sieve i h t iS x y f == Sieve-unc (norm↓ i h t iS) x y f
Sieve-norm↓-ptwise i h (1+ t) iS x y f = idp
Sieve-norm↓-ptwise i O O iS x y f = idp
Sieve-norm↓-ptwise i (1+ h) O iS x y f
 rewrite norm↓-skolem i (1+ h) O iS
 with x ≟-ℕ i
... | inr x≠i = idp
... | inl idp
      with y ≤? height (norm↓ i h (Hom-size i h) (shape-from-next-h iS))
         | y ≤? 1+ h
...      | inr y≰h↓ | inl (inl idp) = idp
...      | inr y≰h↓ | inl (inr y<Sh) = {!this one is a problem if we use the
                                       current def of norm↓!}
...      | inr y≰h↓ | inr y≰Sh = idp
...      | inl (inl idp) | inl (inl p) = {!!}
...      | inl (inl idp) | inl (inr u) = {!!}
...      | inl (inl idp) | inr h↓≰Sh = {!ok!}
...      | inl (inr u) | inl (inl idp) = {!ok!}
...      | inl (inr u) | inl (inr y<Sh) = idp
...      | inl (inr u) | inr y≰Sh = {!ok!}
{-
      with y ≤? 1+ h      | y ≤? height (norm↓ i h (Hom-size i h)
                                               (shape-from-next-h iS))
...      | inl (inl idp)  | inl (inl p) = {!!}
...      | inl (inl idp)  | inl (inr u) = {!!}
...      | inl (inl idp)  | inr y≰h↓ = idp
...      | inl (inr y<Sh) | inl y≤h↓ = {!!}
...      | inl (inr y<Sh) | inr y≰h↓ = {!!}
...      | inr y≰Sh       | inl y≤h↓ = {!!}
...      | inr y≰Sh       | inr y≰h↓ = idp
-}

{- Principal sieves -}

⦅_⦆ : {x y : ℕ} → Hom x y → DSM
⦅_⦆ {x} f u _ g with u ≟-ℕ x
... | inl idp = to-Bool (g factors-through? f)
... | inr _ = false

⦅_⦆-correct : ∀ {x y z : ℕ} (f : Hom x y)
              → (g : Hom x z)
              → ⟦ ⦅ f ⦆ ⟧ g == to-Bool (g factors-through? f)
⦅_⦆-correct {x} {y} {z} f g with x ≟-ℕ x
... | inl p rewrite is-set-UIP Ob-is-set p = idp
... | inr ¬p = ⊥-rec (¬p idp)
-- Can also reify the above into (g ∈ₘ ⦅ f ⦆) ≃ ∥ g factors-through f ∥
