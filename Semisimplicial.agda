{-# OPTIONS --without-K --termination-depth=2 #-}

module Semisimplicial where

open import CwF public
open import Sieves

module _ {i} (C : WildCategory {i})
  (cwf : WildCwFStructure C)
  (pistruct : PiStructure cwf)
  (sigmastruct : SigmaStructure cwf)
  (ustruct : UStructure cwf)
  where
  open WildCwFStructure cwf
  open PiStructure pistruct
  open SigmaStructure sigmastruct
  open UStructure ustruct

  SST : ℕ → Con
  Sk  : (n k t : ℕ) ⦃ tpos : O < t ⦄ → is-sieve n k t → Ty (SST k)

  -- (shape+ n) is the shape of the type of (n+1)-fillers
  shape+ : (n : ℕ) → Ty (SST n)
  shape+ n = (Sk (1+ n) n (2+ n) (is-last-sieve n)) ̂→ U

  SST O = ◆ ∷ U
  SST (1+ n) = SST n ∷ shape+ n

  Sk (1+ n) O (1+ O) _  = el (υ U ↓)
  Sk (1+ n) O (2+ t) iS = Sk (1+ n) O (1+ t) (prev-is-sieve-t iS) ̂× el (υ U ↓)

  Sk (1+ n) (1+ k) (1+ O) iS@(Sk<Sn , _) =
    ̂Σ[ s ∈ prev-Sk ]
      let
        A : Tm {SST k ∷ shape+ k ∷ prev-Sk} (shape+ k ↑ ↑)
        A = (υ (shape+ k) ↑ₜ)
      in
        {!s!}
    where
      -- Shape of the full k-skeleton of Δ⁽ⁿ⁺¹⁾
      prev-Sk : Ty (SST k ∷ shape+ k)
      prev-Sk = Sk (1+ n) k (binom (2+ n) (1+ k))
                   ⦃ binom>O (2+ n) (1+ k) (<-trans Sk<Sn ltS) ⦄
                   (prev-is-sieve-k iS) ↑

  Sk (1+ n) (1+ k) (2+ t) (Sk<Sn , 2+≤binom) = {!!}
