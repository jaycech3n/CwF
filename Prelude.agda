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


{- Maybe -}

abstract
  Maybe : Type i → Type i
  Maybe A = A ⊔ ⊤

  none : {A : Type i} → Maybe A
  none = inr tt

  some : {A : Type i} → A → Maybe A
  some a = inl a

  Maybe-elim : {A : Type i} {B : Type j}
               → Maybe A → B → (A → B) → B
  Maybe-elim {A = A} m b f = ⊔-elim {A = A} {B = ⊤} f (λ _ → b) m


{- Triples -}

module _ {A : Type i} {B : A → Type j} {C : {a : A} (b : B a) → Type k} where
  2nd : (u : Σ[ a ∈ A ] Σ[ b ∈ B a ] C b) → B (fst u)
  2nd = fst ∘ snd

  3rd : (u : Σ[ a ∈ A ] Σ[ b ∈ B a ] C b) → C (fst (snd u))
  3rd = snd ∘ snd


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
