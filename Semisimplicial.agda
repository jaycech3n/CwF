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

  -- I'm a bit lost with how exactly these should be written in terms of contexts.
  -- Let's go back to types first.
  SST     : ℕ → Con
  partial : (n : ℕ)              -- Building (∂)Δⁿ...
            (k : Fin n)          -- up to the k-th level (0 ≤ k < n),
          → Fin (S n ch S (k ↗)) -- up to the ith k-face (0 ≤ i < (S n) ch (S k)).
          → Con

  SST   O   = ◆ ∷ U
  SST (S n) = ?

  partial (S n) (O , _) (O , _) = SST O ∷ el (ν ↗)
  partial (S n) (O , x) (S i , y) = {!!} -- ν {partial (S n) (O , x) (i , ?)} ↗
  partial (S n) (S k , snd₁) = {!!}
