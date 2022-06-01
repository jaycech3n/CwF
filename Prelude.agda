{-# OPTIONS --without-K #-}

module Prelude where

open import HoTT
  renaming
  ( lsucc          to lsuc
  ; transport      to tr
  ; transp-∙       to tr-∙
  ; to-transp      to to-tr
  ; from-transp    to from-tr
  ; [_]            to ‖_‖
  ; ℕ-has-dec-eq   to _≟-ℕ_
  ; Fin-has-dec-eq to _≟-Fin_
  ; <-dec          to _<?_
  ; ≤-dec          to _≤?_ )
  public

private
  variable
    ℓ₁ ℓ₂ ℓ₃ : ULevel


{- Notation -}

pattern 1+ n = S n
pattern 2+ n = S (S n)

Σ-syntax = Σ
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B


{- Inspect -}

-- The inspect idiom, copied from the Agda standard library

record Reveal_·_is_ {A : Type ℓ₁} {B : A → Type ℓ₂}
  (f : (x : A) → B x) (x : A) (y : B x) : Type (lmax ℓ₁ ℓ₂)
  where
  constructor ▹
  field eq : f x == y

inspect : ∀ {A : Type ℓ₁} {B : A → Type ℓ₂}
          (f : (x : A) → B x) (x : A) → Reveal f · x is f x
inspect f x = ▹ idp


{- Triples -}

module _ {A : Type ℓ₁} {B : A → Type ℓ₂} {C : {a : A} (b : B a) → Type ℓ₃} where
  2nd : (u : Σ[ a ∈ A ] Σ[ b ∈ B a ] C b) → B (fst u)
  2nd = fst ∘ snd

  3rd : (u : Σ[ a ∈ A ] Σ[ b ∈ B a ] C b) → C (2nd u)
  3rd = snd ∘ snd


{- Coproducts -}

inl= : {A : Type ℓ₁} {B : Type ℓ₂} {a a' : A} → a == a' → inl a == inl a' :> A ⊔ B
inl= idp = idp

inr= : {A : Type ℓ₁} {B : Type ℓ₂} {b b' : B} → b == b' → inr b == inr b' :> A ⊔ B
inr= idp = idp


{- Maybe -}

-- Could make this dependent, but don't need it.

Maybe : Type ℓ₁ → Type ℓ₁
Maybe A = A ⊔ ⊤

some : {A : Type ℓ₁} → A → Maybe A
some a = inl a

pattern none = inr tt

Maybe-elim : {A : Type ℓ₁} {B : Type ℓ₂}
             → Maybe A → B → (A → B) → B
Maybe-elim m b f = ⊔-elim f (λ _ → b) m

default : {A : Type ℓ₁} {B : Type ℓ₂} → B → (A → B) → Maybe A → B
default _ f (inl a) = f a
default b f none = b

some≠none : {A : Type ℓ₁} {a : A} → some a ≠ none
some≠none {a = a} = inl≠inr a tt


{- Decidable types -}

True : {A : Type ℓ₁} → Dec A → Bool
True (inl _) = true
True (inr _) = false


{- Rewriting transports -}

module _ {A : Type ℓ₁} {B : A → Type ℓ₂} {x y : A} where
  tr!-tr     : {b : B x} (p : x == y)
               → tr B (! p) (tr B p b) == b

  tr-tr!     : {b : B y} (p : x == y)
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
