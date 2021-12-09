{-# OPTIONS --without-K #-}

module bht.SCT where

open import CwF public
open import bht.NiceIndexCategory
open import bht.Sieves

module _ {i}
  ⦃ I : NiceIndexCategory {i} ⦄
  ( C : WildCategory {i} )
  ( cwf         : WildCwFStructure C )
  ( pistruct    : PiStructure cwf    )
  ( sigmastruct : SigmaStructure cwf )
  ( unitstruct  : UnitStructure cwf  )
  ( ustruct     : UStructure cwf     )
  where
  open NiceIndexCategory I
  open WildCwFStructure cwf
  open PiStructure pistruct
  open SigmaStructure sigmastruct
  open UnitStructure unitstruct
  open UStructure ustruct

  SCT : ℕ → Con
  Sk  : (b h t : ℕ) → is-sieve b h t → Ty (SCT (1+ h))
  -- M b is the "matching object" of the diagram (SCT b).
  M   : (b : ℕ) → Ty (SCT b)

  -- The context SCT n = (A₀, A₁, ..., Aₙ₋₁) consists of all fillers of cells up
  -- to (and including) "dimension" (n-1).
  SCT O = ◆
  SCT (1+ n) = SCT n ∷ M n ̂→ U

  Sk = {!!}

  M O = ̂⊤
  M (1+ b) = Sk (1+ b) b (Hom-size b (1+ b)) (is-sieve-bhtmax lteS)
