{-# OPTIONS --without-K #-}

module hott.Bool where

open import hott.Base


not : Bool → Bool
not true = false
not false = true

_and_ : Bool → Bool → Bool
true and b = b
false and _ = false

_or_ : Bool → Bool → Bool
true or _ = true
false or b = b
