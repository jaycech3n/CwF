{-# OPTIONS --without-K #-}

module Prelude where

open import HoTT renaming
  ( lsucc to lsuc
  ; transport to tr ) public

tr-!-tr : ∀ {i j} {A : Type i} {B : A → Type j} {x y : A} (p : x == y) {b : B x}
          → tr B (! p) (tr B p b) == b
tr-!-tr idp = idp

tr-tr-! : ∀ {i j} {A : Type i} {B : A → Type j} {x y : A} (p : x == y) {b : B y}
          → tr B p (tr B (! p) b) == b
tr-tr-! idp = idp
