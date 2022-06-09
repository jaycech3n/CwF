{-# OPTIONS --without-K #-}

module hott.Transport where

open import hott.Base

private
  variable ℓ ℓ₁ ℓ₂ ℓ₃ : ULevel


{- Rewriting transports -}

module _ {A : Type ℓ₁} {B : A → Type ℓ₂} {x y : A} where
  tr!-tr : {b : B x} (p : x == y)
           → tr B (! p) (tr B p b) == b

  tr-tr! : {b : B y} (p : x == y)
           → tr B p (tr B (! p) b) == b

  tr==-==tr! : ∀ {b} {b'} {p : x == y}
               → tr B p b == b'
               → b == tr B (! p) b'

  tr!==-==tr : ∀ {b} {b'} {p : x == y}
               → tr B (! p) b == b'
               → b == tr B p b'

  ==tr-tr!== : ∀ {b} {b'} {p : x == y}
               → b == tr B p b'
               → tr B (! p) b == b'

  ==tr!-tr== : ∀ {b} {b'} {p : x == y}
               → b == tr B (! p) b'
               → tr B p b == b'

  tr!-tr idp = idp
  tr-tr! idp = idp
  tr==-==tr! {p = idp} idp = idp
  tr!==-==tr {p = idp} idp = idp
  ==tr-tr!== {p = idp} idp = idp
  ==tr!-tr== {p = idp} idp = idp

tr-ap-∙ : {A : Type ℓ₁} {B : Type ℓ₂} {f : A → B} {C : B → Type ℓ₃}
          {x y z : A} (p : x == y) (q : y == z) (c : C (f x))
          → tr C (ap f (p ∙ q)) c == tr C (ap f q) (tr C (ap f p) c)
tr-ap-∙ idp idp c = idp
