{-# OPTIONS --without-K #-}

open import SuitableSemicategories
open import CwF

module scratch-SCT {ℓ}
  ⦃ I : SuitableSemicategory ⦄
  ( C : WildCategory {ℓ} )
  ( cwf      : WildCwFStructure C )
  ( pistr    : PiStructure cwf    )
  ( sigmastr : SigmaStructure cwf )
  ( unitstr  : UnitStructure cwf  )
  ( ustr     : UStructure cwf     )
  where

open import Shapes-scratch
open SuitableSemicategory I
open WildCwFStructure cwf
open PiStructure pistr
open SigmaStructure sigmastr
open UnitStructure unitstr
open UStructure ustr

M[_,_,_] : (i h t : ℕ) (iS : is-shape i h t) → Con
M : ℕ → Con
SCT : ℕ → Con
A : (n : ℕ) → Ty (SCT n)

SCT n = M n ∷ U

A n = el ((υ U) ↓)

M O = ◆
M (1+ n) = M[ 1+ n , n , Hom-size (1+ n) n ] (full-shape (1+ n) n ltS)

M[ i , h , 1+ t ] iS = {!!}
M[ i , 1+ h , O ] iS = M[ i , h , Hom-size i h ] (shape-from-next-h iS)
M[ i , O , O ] iS = {!!}
