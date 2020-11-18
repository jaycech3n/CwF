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

  {-
  The elements of an n-semisimplicial type are tuples (A₀, A₁, ..., An) where
  the elements of Aₖ have k-simplicial "shape".

  Δⁿ has C(n+1,k) faces of dimension k.  A k-face is indexed by its position in
  the list of k-faces ordered lexicographically along their vertices.
  -}  
  SST : ℕ → Ty ◆
  ∂Δ[1+_] : (n : ℕ) → Tm ((SST n) [ p ]) → Ty (◆ ∷ SST n)

  SST   O   = U
  SST (S n) = ̂Σ (SST n) (∂Δ[1+ n ] ν ̂→ U)
  
  ∂Δ[1+   O  ] A₀ = el (A₀ ↗) ̂× el (A₀ ↗)
  ∂Δ[1+ (S n)] As = {!!}

  {- Build partial shapes of ∂Δⁿ level-wise, face by face. -}
  _ch_ : (n k : ℕ) → ℕ
  O ch O = 1
  O ch (S k) = 0
  (S n) ch O = 1
  (S n) ch (S k) = (n ch (S k)) + (n ch k)

  private
  -- Get nth item of right-associated tuple. Maybe this will be easier with the
  -- context formulation instead.
    nth : {!!}
    nth = {!!}

  -- Does this need to be mutual with the rest?
  shape : (n : ℕ)              -- Building up ∂Δⁿ
          (k : Fin n)          -- Now on the k-faces
        → Fin (S n ch S (k ↗)) -- The ith k-face (indexed from zero)
        → Tm (SST n)
        → Ty ◆
  shape (S n) (O , O<Sn) = {!!}
  shape (S n) (S k , snd₁) = {!!}
