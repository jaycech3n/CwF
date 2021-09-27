{-# OPTIONS --without-K #-}

module Prelude where

open import HoTT
  renaming
  ( lsucc        to lsuc
  ; transport    to tr
  ; transp-∙     to tr-∙
  ; to-transp    to to-tr
  ; from-transp  to from-tr
  ; [_]          to ∥_∥
  ; ℕ-has-dec-eq to ≟-ℕ )
  public


pattern 1+ n = S n
pattern 2+ n = S (S n)

private
  variable
    i j k : ULevel
    A : Type i


-- n-fold composition

fold-∘ : (B : ℕ → Type j)
         (f : {n : ℕ} → B n → B (1+ n))
         (m : ℕ)
         {n : ℕ}
         → B n → B (m + n)
fold-∘ B f    O   {n} = idf (B n)
fold-∘ B f (1+ m) {n} = f ∘ (fold-∘ B f m)


{- Rewriting transports -}

module _ {B : A → Type j} {x y : A} where

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

tr-ap-∙ : {B : Type j} {f : A → B} {C : B → Type k} {x y z : A}
          (p : x == y) (q : y == z) (c : C (f x))
          → tr C (ap f (p ∙ q)) c == tr C (ap f q) (tr C (ap f p) c)
tr-ap-∙ idp idp c = idp
