{-# OPTIONS --without-K #-}

{--- Semisimplicial types in internal CwFs---}

module Semisimplicial where

open import CwF
open import Sieves

module _ {i} (C : WildCategory {i}) (cwF : WildCwFStructure C)
  (piStr : PiStructure cwF) (sigmaStr : SigmaStructure cwF)
  (uStr : UStructure cwF)
  where
  open WildCwFStructure cwF
  open PiStructure piStr
  open SigmaStructure sigmaStr
  open UStructure uStr

  SST    : ℕ → Con
  SST₋   : ℕ → Con
  X      : (i n : ℕ) ⦃ le : i ≤ n ⦄ → Ty (SST n)
  A      : (i n : ℕ) ⦃ le : i ≤ n ⦄ → Tm (X i n)
  sk     : (k n : ℕ) ⦃ nz : O < n ⦄ ⦃ lt : k < n ⦄ → Ty (SST₋ n)
  coords : (k n : ℕ) ⦃ nz : O < n ⦄ ⦃ lt : k < n ⦄ → List {!!}

  SST₋ O = ◆
  SST₋ (S n) = SST n

  SST O = ◆ ∷ U
  SST (S n) = SST n ∷ (sk n (S n) ̂→ U)

  X O O = U [ p ]
  X O (S n) = X O n [ p ]
  -- For i < n:
  X (S i) (S n) ⦃ inr x ⦄ = X (S i) n ⦃ S<S-dec-r x ⦄ [ p ]
  -- For i = n:
  X (S i) (S n) ⦃ inl _ ⦄ = (sk n (S n) ̂→ U)[ p ]

  XO=U : (n : ℕ) → X O n == U
  XO=U O     = U-[]
  XO=U (S n) = X O n [ p ]
             =⟨ XO=U n |in-ctx _[ p ] ⟩ U [ p ]
             =⟨ U-[] ⟩ U =∎

  instance
    XO-coercion : ∀ {n} → Coerceable (Tm (X O n)) (Tm U)
    coerce ⦃ XO-coercion {n} ⦄ = tr Tm (XO=U n)

  instance
    XOp-coercion : ∀ {n}
                 → Coerceable (Tm (X O n [ p :> Sub (SST (S n)) (SST n)]))
                             (Tm U)
    coerce ⦃ XOp-coercion {n} ⦄ = tr Tm (ap _[ p ] (XO=U n) ∙ U-[])

  A O O = ν
  A O (S n) = A O n [ p ]ₜ
  A (S i) (S n) ⦃ inr x ⦄ = A (S i) n ⦃ S<S-dec-r x ⦄ [ p ]ₜ
  A (S i) (S n) ⦃ inl _ ⦄ = ν

  sk k n = {!!}
  coords k n = {!!}
