{-# OPTIONS --without-K #-}

open import SuitableSemicategories

module Sieves ⦃ I : SuitableSemicategory ⦄ where
open SuitableSemicategory I

open import DSM _≟-ℕ_ public
open import Shapes public


{- Linear sieves -}

sieve[_,_,_] : (i h t : ℕ) (iS : is-shape i h t) → DSM
sieve[ i , h , t ] iS x y = χ (x ≟-ℕ i) (y ≤? h)
  where
  χ : ∀ {x y} → Dec (x == i) → Dec (y ≤ h) → Hom x y → Bool
  χ (inl idp) (inl (inl y=h)) f = to-Bool (ℕ-idx-of f <? t)
  χ (inl idp) (inl (inr y<h)) _ = true
  χ (inl idp) (inr y≰h) _ = false
  χ (inr x≠i) _ _ = false

sieve-unc : Shape → DSM
sieve-unc ((i , h , t) , iS) = sieve[ i , h , t ] iS

sieve-norm-eq : ∀ i h t iS → sieve[ i , h , t ] iS == sieve-unc (norm i h t iS)
sieve-norm-eq i h (1+ t) iS = idp
sieve-norm-eq i O O iS = idp
sieve-norm-eq i (1+ h) O iS = DSM= ptwise
  where
  ptwise : ∀ x y f
    → sieve[ i , 1+ h , O ] iS x y f
      == sieve-unc ((i , h , Hom-size i h) , shape-from-next-h iS) x y f
  ptwise x y f
   with x ≟-ℕ i | y ≤? h        | y ≤? 1+ h
  ... | inl idp | inl (inl idp) | inl (inr _)
        rewrite reflect (idx-of<Hom-size f) (ℕ-idx-of f <? Hom-size x y) = idp
  ... | inl idp | inl (inl idp) | inr h≮Sh = ⊥-rec (h≮Sh lteS)
  ... | inl idp | inl (inr y<h) | inl (inl idp) = ⊥-rec (S≮ y<h)
  ... | inl idp | inl (inr _)   | inl (inr _) = idp
  ... | inl idp | inl (inr y<h) | inr y≰Sh = ⊥-rec (y≰Sh (inr (ltSR y<h)))
  ... | inl idp | inr _         | inl (inl _) = idp
  ... | inl idp | inr y≰h       | inl (inr y<Sh) = ⊥-rec (y≰h (<S→≤ y<Sh))
  ... | inl idp | inr _         | inr _ = idp
  ... | inr x≠i | _             | _ = idp

empty-sieve-eq : ∀ i iS → sieve[ i , O , O ] iS == Ø
empty-sieve-eq i iS = DSM= ptwise
  where
  ptwise : ∀ x y f → sieve[ i , O , O ] iS x y f == Ø x y f
  ptwise x y f with x ≟-ℕ i | y ≤? O
  ... | inl idp | inl (inl idp) = idp
  ... | inl idp | inr _ = idp
  ... | inr x≠i | _ = idp


{- Principal sieves -}

⦅_⦆ : {x y : ℕ} → Hom x y → DSM
⦅_⦆ {x} f u v = χ (u ≟-ℕ x)
  where
  χ : ∀ {u v} → Dec (u == x) → Hom u v → Bool
  χ (inl idp) g = to-Bool (g factors-through? f)
  χ (inr _) g = false

-- Test
⦅_⦆-correct : ∀ {x y z : ℕ} (f : Hom x y)
              → (g : Hom x z)
              → ⟦ ⦅ f ⦆ ⟧ g == to-Bool (g factors-through? f)
⦅_⦆-correct {x} {y} {z} f g with x ≟-ℕ x
... | inl p rewrite is-set-UIP Ob-is-set p = idp
... | inr ¬p = ⊥-rec (¬p idp)
-- Can also reify the above into (g ∈ₘ ⦅ f ⦆) ≃ ∥ g factors-through f ∥
