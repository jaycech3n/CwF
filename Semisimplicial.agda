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
    shape n ─ Partial subskeletons of Δⁿ, indexed by sieves on [n]. Used to
               define Sk n.
    Sk n    ─ (n-1)-skeleton of Δⁿ.
  -}
  SST   : ℕ → Con
  shape : (n : ℕ) → Sieve n → Ty (SST n)
  Sk    : (n : ℕ) → Ty (SST n)

  SST 0 = ◆ ∷ U
  SST (S n) = SST n ∷ (Sk n ̂→ U)

  -- NOTE I think the indexing is a bit wonky, possibly also in Sieves.agda.
  -- Fix this.
  shape 0 ()
  shape 1 ((0 , _) , (0 , _)) = {!!}
  shape 1 ((0 , _) , (S t , _)) = {!!}
  shape 1 ((S fst₁ , snd₁) , t) = {!!}
  shape (S (S n)) x = {!!}

  Sk n = shape n {!correct maximum sieve index!}
