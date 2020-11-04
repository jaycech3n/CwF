{-# OPTIONS --without-K #-}

module Prelude where

open import HoTT renaming
  ( lsucc     to lsuc
  ; transport to tr
  ; transp-∙  to tr-∙ ) public

{- Equality reasoning -}
module _ {i j : ULevel} {A : Type i} {B : A → Type j} {x y : A} where
  tr-!-tr : ∀ {b} (p : x == y) → tr B (! p) (tr B p b) == b
  tr-!-tr idp = idp

  tr-tr-! : ∀ {b} (p : x == y) → tr B p (tr B (! p) b) == b
  tr-tr-! idp = idp

  tr!=-if-=tr : ∀ {b b'} {p : x == y} (p' : b == tr B p b') → tr B (! p) b == b'
  tr!=-if-=tr {p = idp} idp = idp

  tr=-if-=tr! : ∀ {b b'} {p : x == y} (p' : b == tr B (! p) b') → tr B p b == b'
  tr=-if-=tr! {p = idp} idp = idp

  =tr!-if-tr= : ∀ {b b'} {p : x == y} (p' : tr B p b == b') → b == tr B (! p) b'
  =tr!-if-tr= {p = idp} idp = idp

  =tr-if-tr!= : ∀ {b b'} {p : x == y} (p' : tr B (! p) b == b') → b == tr B p b'
  =tr-if-tr!= {p = idp} idp = idp

tr-ap-∙ : ∀ {i j k} {A : Type i} {B : Type j} {f : A → B} {C : B → Type k}
            {x y z : A} (p : x == y) (q : y == z) (c : C (f x))
          → tr C (ap f (p ∙ q)) c == tr C (ap f q) (tr C (ap f p) c)
tr-ap-∙ idp idp c = idp
