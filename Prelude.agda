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
  ; ≤-dec          to _≤?_ )
  public

private
  variable
    i j k : ULevel


{- Notation -}

pattern 1+ n = S n
pattern 2+ n = S (S n)

Σ-syntax = Σ
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B


{- Triples -}

module _ {A : Type i} {B : A → Type j} {C : {a : A} (b : B a) → Type k} where
  2nd : (u : Σ[ a ∈ A ] Σ[ b ∈ B a ] C b) → B (fst u)
  2nd = fst ∘ snd

  3rd : (u : Σ[ a ∈ A ] Σ[ b ∈ B a ] C b) → C (fst (snd u))
  3rd = snd ∘ snd


{- Coproducts -}

inl= : {A : Type i} {B : Type j} {a a' : A} → a == a' → inl a == inl a' :> A ⊔ B
inl= idp = idp

inr= : {A : Type i} {B : Type j} {b b' : B} → b == b' → inr b == inr b' :> A ⊔ B
inr= idp = idp


{- Maybe -}

-- Could make this dependent, but don't need it.

Maybe : Type i → Type i
Maybe A = A ⊔ ⊤

some : {A : Type i} → A → Maybe A
some a = inl a

pattern none = inr tt

Maybe-elim : {A : Type i} {B : Type j}
             → Maybe A → B → (A → B) → B
Maybe-elim m b f = ⊔-elim f (λ _ → b) m

default : {A : Type i} {B : Type j} → B → (A → B) → Maybe A → B
default _ f (inl a) = f a
default b f none = b

some≠none : {A : Type i} {a : A} → some a ≠ none
some≠none {a = a} = inl≠inr a tt


{- Decidable types -}

True : {A : Type i} → Dec A → Bool
True (inl _) = true
True (inr _) = false


{- Rewriting transports -}

module _ {A : Type i} {B : A → Type j} {x y : A} where
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


tr-ap-∙ : {A : Type i} {B : Type j} {f : A → B} {C : B → Type k}
          {x y z : A} (p : x == y) (q : y == z) (c : C (f x))
          → tr C (ap f (p ∙ q)) c == tr C (ap f q) (tr C (ap f p) c)
tr-ap-∙ idp idp c = idp
