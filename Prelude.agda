{-# OPTIONS --without-K #-}

module Prelude where

open import HoTT renaming
  ( lsucc to lsuc
  ; transport to tr ) public

{- Equality reasoning -}
private
  variable
    i j : ULevel
    A : Type i
    B : A → Type j
    x y : A

tr-!-tr : ∀ {b} (p : x == y) → tr B (! p) (tr B p b) == b
tr-!-tr idp = idp

tr-tr-! : ∀ {b} (p : x == y) → tr B p (tr B (! p) b) == b
tr-tr-! idp = idp

move-tr-l : ∀ {b b'} {p : x == y} (p' : b == tr B p b') → tr B (! p) b == b'
move-tr-l {p = idp} idp = idp

move-tr-!-l : ∀ {b b'} {p : x == y} (p' : b == tr B (! p) b') → tr B p b == b'
move-tr-!-l {p = idp} idp = idp

move-tr-r : ∀ {b b'} {p : x == y} (p' : tr B p b == b') → b == tr B (! p) b'
move-tr-r {p = idp} idp = idp

move-tr-!-r : ∀ {b b'} {p : x == y} (p' : tr B (! p) b == b') → b == tr B p b'
move-tr-!-r {p = idp} idp = idp
