{-# OPTIONS --without-K --termination-depth=2 #-}

module Semisimplicial where

open import CwF public
open import Sieves

module _ {i} (C : WildCategory {i})
  (cwf : WildCwFStructure C)
  (pistruct : PiStructure cwf)
  (sigmastruct : SigmaStructure cwf)
  (unitstruct : UnitStructure cwf)
  (ustruct : UStructure cwf)
  where
  open WildCwFStructure cwf
  open PiStructure pistruct
  open SigmaStructure sigmastruct
  open UnitStructure unitstruct
  open UStructure ustruct

  SST : ℕ → Con
  -- Why does decoupling work? Some explanation would be good!
  Sk  : (n k t : ℕ) → is-sieve n k t → (l : ℕ) → k ≤ l → Ty (SST l)

  -- Uncurried Maybe form of Sk
  Sk-aux : (s : Maybe Sieve) (l : ℕ) → default 0 get-k s ≤ l → Ty (SST l)
  Sk-aux (inl ((n , k , t) , iS)) = ?
  Sk-aux none = ?

  Sk→ : (n k t : ℕ) (iS : is-sieve n k t) (l : ℕ) (k≤l : k ≤ l)
        → {m : ℕ} (f : m →+ n)
        → Tm (Sk n k t iS l k≤l) → Tm (Sk-aux ([ n , k , t ]∩[ m , f ] iS) l k≤l)

  -- (shape+ n) is the shape of the type of (n+1)-fillers
  shape+ : (n : ℕ) → Ty (SST n)
  shape+ n = (Sk (1+ n) n (binom (2+ n) (1+ n)) (last-is-sieve _ _ lteS)) ̂→ U

  SST O = ◆ ∷ U
  SST (1+ n) = SST n ∷ shape+ n

  Sk = ?
  Sk→ = ?
