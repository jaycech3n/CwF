{-# OPTIONS --without-K #-}

{--- Semisimplicial types in internal CwFs ---}

module Semisimplicial where

open import CwF

module _ {i} (C : WildCategory {i}) (cwF : WildCwFStructure C)
  (piStr : PiStructure cwF) (sigmaStr : SigmaStructure cwF)
  (uStr : UStructure cwF)
  where
  open WildCwFStructure cwF
  open PiStructure piStr
  open SigmaStructure sigmaStr
  open UStructure uStr

  SST : ∀ {Γ} → ℕ → Ty Γ
  SST   O   = U
  SST (S n) = ̂Σ (SST n) ({!shape of the boundary of ∂Δⁿ!} ̂→ U)
