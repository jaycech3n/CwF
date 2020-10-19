{-# OPTIONS --without-K #-}

module CwF where

open import Category

{- Categories with families as a generalized algebraic theory. -}

record StrictCwF {i} : Type (lsuc i) where
  {- Contexts and substitutions -}
  field
    C : StrictCategory {i}
  open StrictCategory C renaming
    ( Ob         to Con
    ; Hom        to Sub
    ; Ob-is-set  to Con-is-set
    ; Hom-is-set to Sub-is-set
    ) public

  
