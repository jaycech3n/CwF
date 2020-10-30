{-# OPTIONS --without-K #-}

module Prelude where

open import HoTT renaming
  ( lsucc to lsuc
  ; transport to tr ) public

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

