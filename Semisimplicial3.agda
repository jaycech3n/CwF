{-# OPTIONS --without-K #-}

{--- Semisimplicial types in internal CwFs, Take 3 ---}

module Semisimplicial3 where

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

  SST   : ℕ → Con
  SST₋  : ℕ → Con
  X     : (i n : ℕ) ⦃ le : i ≤ n ⦄ → Ty (SST n)
  A     : (i n : ℕ) ⦃ le : i ≤ n ⦄ → Tm (X i n)

  {- Sieves indexed by n, h, t:
     n -- 0 < n; sieves into [n] aka shapes in Δⁿ
     h -- 1 ≤ h ≤ n; all arrows [i] → [n] for 0 ≤ i < h are present
     t -- number of arrows [h] → [n] (0 ≤ t ≤ binom (n+1) (h+1))
  -}

  shape : (n h t : ℕ) ⦃ nz : O < n ⦄ ⦃ hz : O < h ⦄ ⦃ le : h ≤ n ⦄ → Ty (SST₋ n)
  -- coord : (n h t : ℕ) ⦃ nz : O < n ⦄ ⦃ hz : O < h ⦄ ⦃ le : h ≤ n ⦄ → {!!}

  SST₋ O = ◆
  SST₋ (S n) = SST n

  SST O = ◆ ∷ U
  SST (S n) = SST n ∷ (shape (S n) (S n) O ⦃ le = lteE ⦄ ̂→ U)

  X O O = U [ p ]
  X O (S n) = X O n [ p ]
  -- For i < n:
  X (S i) (S n) ⦃ inr x ⦄ = X (S i) n ⦃ S<S-dec-r x ⦄ [ p ]
  -- For i = n:
  X (S i) (S n) ⦃ inl _ ⦄ = (shape (S n) (S n) O ̂→ U)[ p ]

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

  shape (S n) (S O) O = el (coerce ⦃ XO-coercion {n} ⦄ (A O n)) ˣ S (S n)
  shape (S n) (S O) (S t) = {!!}
  shape (S n) (S (S h)) t = {!!}

  ∂face = {!!}
