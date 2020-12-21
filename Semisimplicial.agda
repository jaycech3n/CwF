{-# OPTIONS --without-K #-}

{--- Semisimplicial types in internal CwFs ---}

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

  {-
  We mutually define the following:
    SST n   ─ The context (A₀ : U, A₁ : A₀ × A₀ → U, ..., Aₙ : ... → U).
    A n     ─ Aₙ as above.
    X n     ─ The type of Aₙ.
    shape n ─ Partial subskeletons of Δⁿ as Σ-types indexed by sieves on [n].
              Used to define Sk n. Its type as written below is isomorphic to
              (n : ℕ) → Sieve n → Ty (SST₋ n).
    Sk n    ─ (n-1)-skeleton of Δⁿ.

  SST₋ is an intermediate construct to more conveniently type shape and Sk.
  By definition, SST₋ n = SST (n-1) for n ≥ 1.
  -}
  SST₋  : ℕ → Con
  SST   : ℕ → Con
  X     : (n : ℕ) → Ty (SST n)
  A     : (n : ℕ) → Tm (X n)
  shape : (n h t : ℕ) → h < n → t < S n ch S h → Ty (SST₋ n)
  Sk    : (n : ℕ) → {{0 < n}} → Ty (SST₋ n)

  SST₋ O = ◆
  SST₋ (S O) = ◆ ∷ U
  SST₋ (S (S n)) = SST₋ (S n) ∷ (Sk (S n) ̂→ U)

  SST n = SST₋ (S n)

  X O = U [ p ]
  X (S n) = (Sk (S n) ̂→ U) [ p ]

  A O = ν
  A (S n) = ν

  shape O _ _ ()
  shape 1 (S h) t (ltSR ())
  shape 1 0 0 = λ _ _ →  el (A O ↗)
  shape 1 O (S t) = λ p q → shape 1 O t p (<-dec-l q) ̂× el (A O ↗)
  shape (S (S n)) O t = λ p q → {!shape (S n) 0 !}
  shape (S (S n)) (S h) t _ _ = {!!}

  Sk (S n) = shape (S n) n (S n)
                   ltS
                   (tr (S n <_) (! (Sn-ch-n (S n))) (<-ap-S ltS))
