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
              Used to define Sk n.
    Sk n    ─ (n-1)-skeleton of Δⁿ.

  SST₋ is an intermediate construct to more conveniently type shape and Sk.
  By definition, SST₋ n = SST (n-1) for n ≥ 1.
  -}
  SST₋  : ℕ → Con
  SST   : ℕ → Con
  X     : (n : ℕ) → Ty (SST n)
  A     : (n : ℕ) → Tm (X n)

  {- Nicolai: adding this TERMINATING pragma has allowed me 
     to fill what was hole #0. This is of course not a good solution,
     we need to convince the termination checker honestly and remove
     this pragma. For that, it's probably enough to curry the function
     `shape`.
     When one wants to define
       f : ℕ → ℕ → whatever
       g : ℕ × ℕ → whatever
     by recursion on both ℕ's, then Agda has a much harder time to
     see that g terminates than f.
  -}
  {-# TERMINATING #-}
  shape : (n : ℕ) → Sieve n → Ty (SST₋ n)
  Sk    : (n : ℕ) → Ty (SST₋ n)

  SST₋ O = ◆
  SST₋ (S O) = ◆ ∷ U
  SST₋ (S (S n)) = SST₋ (S n) ∷ (Sk (S n) ̂→ U)

  SST n = SST₋ (S n)

  X O = U [ p ]
  X (S n) = (Sk (S n) ̂→ U) [ p ]

  A O = ν
  A (S n) = ν

  shape O ()
  shape 1 ((O , _) , (O , _))
    = el (tr Tm (U-[] {f = p}) (A O)) -- former hole ?0
      -- !!! Strange error blocks acceptance; normalization issue?
  shape 1 ((O , 0<1) , (S t , St<2))
    = shape 1 ((O , 0<1) , (t , <-dec-l St<2)) ̂× {!!}
      -- !!! Termination checking fails, I think because of how Sieve is
      -- formulated?
  shape 1 ((S h , _) , t)
    = {!!}
  shape (S (S n)) x
    = {!!}

  Sk n = shape n {!correct maximum sieve index!}
