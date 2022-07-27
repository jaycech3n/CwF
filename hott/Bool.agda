{-# OPTIONS --without-K #-}

{--- Booleans, decidable types and boolean reflection ---}

module hott.Bool where

open import hott.Base

private
  variable ℓ : ULevel


{- Bool -}

not : Bool → Bool
not true = false
not false = true

_and_ : Bool → Bool → Bool
true and b = b
false and _ = false

_or_ : Bool → Bool → Bool
true or _ = true
false or b = b


{- Reflection -}

-- Rudimentary boolean reflection

to-Bool : {A : Type ℓ} → Dec A → Bool
to-Bool (inl _) = true
to-Bool (inr _) = false

reflect : {A : Type ℓ} → A → (d : Dec A) → to-Bool d == true
reflect _ (inl a) = idp
reflect x (inr ¬a) = ⊥-rec (¬a x)

and-sym : ∀ a b → (a and b) == (b and a)
and-sym true true = idp
and-sym true false = idp
and-sym false true = idp
and-sym false false = idp

or-sym : ∀ a b → (a or b) == (b or a)
or-sym true true = idp
or-sym true false = idp
or-sym false true = idp
or-sym false false = idp


{- Decidable types -}

=-refl-bool : {A : Type ℓ} (_≟_ : has-dec-eq A) (a : A)
              → to-Bool (a ≟ a) == true
=-refl-bool (_≟_) a with a ≟ a
... | inl _ = idp
... | inr ¬p = ⊥-rec (¬p idp)
