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
    A m n   ─ Aₘ in context SST n (for m ≤ n).
    X m n   ─ The type of Aₘ in SST n (m ≤ n).
    Sk n k  ─ k-skeleton of Δⁿ (n > 0).

  SST₋ is an intermediate construct to more conveniently type Sk. By definition,
  SST₋ n = SST (n-1) for n ≥ 1.
  -}
  SST₋  : ℕ → Con
  SST   : ℕ → Con
  X     : (m n : ℕ) → {m ≤ n} → Ty (SST n)
  A     : (m n : ℕ) {h : m ≤ n} → Tm (X m n {h})
  Sk    : (n k : ℕ) → {{O < n}} → k < n → Ty (SST₋ n)

  SST₋ O = ◆
  SST₋ (S O) = ◆ ∷ U
  SST₋ (S (S n)) = SST₋ (S n) ∷ (Sk (S n) n ltS ̂→ U)

  SST n = SST₋ (S n)

  X O O = U [ p ]
  X O (S n) = X O n {O≤ n} [ p ]
  X (S m) (S n) {inl Sm==Sn} = (Sk (S n) n ltS ̂→ U) [ p ]
  X (S m) (S n) {inr Sm<Sn} = X (S m) n {S<S-dec-r m n Sm<Sn} [ p ]

  A O O = ν :> Tm (X O O {lteE})
  A O (S n) = A O n [ p ]ₜ
  A (S m) (S n) {inl Sm==Sn} = ν :> Tm (X (S m) (S n) {inl Sm==Sn})
  A (S m) (S n) {inr Sm<Sn} = A (S m) n {S<S-dec-r m n Sm<Sn} [ p ]ₜ

  Sk (S O) O _ = el (A O O {lteE} ↗) ̂× el (A O O {lteE} ↗)
  Sk (S (S n)) O _ = (Sk (S n) O (O<S n)) [ p ] ̂× {!morally, another `el (A O)`!}
  Sk n (S k) = {!!}
