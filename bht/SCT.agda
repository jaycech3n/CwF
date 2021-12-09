{-# OPTIONS --without-K --termination-depth=2 #-}

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
  -- M b is the "matching object" of the diagram induced by (SCT b).
  M   : (b : ℕ) → Ty (SCT b)

  -- The context SCT n = (A₀, A₁, ..., Aₙ₋₁) consists of all fillers of cells up
  -- to (and including) "dimension" (n-1).
  SCT O = ◆
  SCT (1+ O) = SCT O ∷ U -- (≅ SCT O ∷ M O ̂→ U, which is less convenient)
  SCT (1+ n@(1+ _)) = SCT n ∷ M n ̂→ U

  Sk b O O iS = ̂⊤
  Sk b O (1+ t) iS = Sk b O t (is-sieve-prev-t iS) ̂× el (υ U ↓)
  Sk b (1+ h) O iS = {!!}
  Sk b (1+ h) (1+ t) iS = {!!}

  M O = ̂⊤
  M (1+ b) = Sk (1+ b) b (Hom-size b (1+ b)) (is-sieve-bhtmax lteS)
