{-# OPTIONS --without-K #-}

module Prelude where

open import HoTT
  hiding ( pred )
  renaming
  ( lsucc       to lsuc
  ; transport   to tr
  ; transp-∙    to tr-∙
  ; to-transp   to to-tr
  ; from-transp to from-tr
  ; [_] to ∥_∥ )
  public

private
  variable
    i j k : ULevel
    A : Type i


{- Notation -}

ex-falso = ⊥-elim


{- Coercions: instance search for automatic transport insertion -}

record Coerce {i j} (A : Type i) (B : Type j) : Type (lmax i j) where
  field coerce : A → B

open Coerce ⦃ ... ⦄ public

_↑ : ∀ {i j} {A B} → ⦃ Coerce {i} {j} A B ⦄ → A → B
t ↑  = coerce t


{- Rewriting transport -}

module _ {B : A → Type j} {x y : A} where

  tr-!-tr : {b : B x} (p : x == y)
            → tr B (! p) (tr B p b) == b
  tr-!-tr idp = idp

  tr-tr-! : {b : B y} (p : x == y)
            → tr B p (tr B (! p) b) == b
  tr-tr-! idp = idp

  tr!=-=tr : ∀ {b} {b'} {p : x == y}
             → b == tr B p b'
             → tr B (! p) b == b'
  tr!=-=tr {p = idp} idp = idp

  tr=-=tr! : ∀ {b} {b'} {p : x == y}
             → b == tr B (! p) b'
             → tr B p b == b'
  tr=-=tr! {p = idp} idp = idp

  =tr!-tr= : ∀ {b} {b'} {p : x == y}
             → tr B p b == b'
             → b == tr B (! p) b'
  =tr!-tr= {p = idp} idp = idp

  =tr-tr!= : ∀ {b} {b'} {p : x == y}
             → tr B (! p) b == b'
             → b == tr B p b'
  =tr-tr!= {p = idp} idp = idp

tr-ap-∙ : {B : Type j} {f : A → B} {C : B → Type k} {x y z : A}
          (p : x == y) (q : y == z) (c : C (f x))
          → tr C (ap f (p ∙ q)) c == tr C (ap f q) (tr C (ap f p) c)
tr-ap-∙ idp idp c = idp
