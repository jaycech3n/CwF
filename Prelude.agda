{-# OPTIONS --without-K #-}

module Prelude where

open import HoTT renaming
  ( lsucc     to lsuc
  ; transport to tr
  ; transp-∙  to tr-∙
  ; to-transp to to-tr
  ; from-transp to from-tr ) public

private
  variable
    i j k : ULevel
    A : Type i

{- Rewriting transports -}
module _ {B : A → Type j} {x y : A} where
  tr-!-tr : {b : B x} (p : x == y) → tr B (! p) (tr B p b) == b
  tr-!-tr idp = idp

  tr-tr-! : {b : B y} (p : x == y) → tr B p (tr B (! p) b) == b
  tr-tr-! idp = idp

  tr!=-if-=tr : ∀ {b} {b'} {p : x == y} (p' : b == tr B p b')
              → tr B (! p) b == b'
  tr!=-if-=tr {p = idp} idp = idp

  tr=-if-=tr! : ∀ {b} {b'} {p : x == y} (p' : b == tr B (! p) b')
              → tr B p b == b'
  tr=-if-=tr! {p = idp} idp = idp

  =tr!-if-tr= : ∀ {b} {b'} {p : x == y} (p' : tr B p b == b')
              → b == tr B (! p) b'
  =tr!-if-tr= {p = idp} idp = idp

  =tr-if-tr!= : ∀ {b} {b'} {p : x == y} (p' : tr B (! p) b == b')
              → b == tr B p b'
  =tr-if-tr!= {p = idp} idp = idp

tr-ap-∙ : {B : Type j} {f : A → B} {C : B → Type k}
          {x y z : A} (p : x == y) (q : y == z) (c : C (f x))
        → tr C (ap f (p ∙ q)) c == tr C (ap f q) (tr C (ap f p) c)
tr-ap-∙ idp idp c = idp

{- PathOver-transport interaction -}
PathOver-tr : {B : A → Type j} {x y z : A}
              {p : x == y} {q : y == z}
              {b' : B z} (b : B x)
            → b == b' [ B ↓ p ∙ q ]
            → tr B p b == b' [ B ↓ q ]
PathOver-tr {p = idp} {q = idp} _ idp = idp
