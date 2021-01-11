{-# OPTIONS --without-K --termination-depth=2 #-}

{--- Semisimplicial types in internal CwFs, Take 2 ---}

module Semisimplicial2 where

open import CwF
open import Sieves

{- Sequences and the combinatorics of faces

It's first important to note that we distinguish between the simplex and
skeletal *shapes* that we're trying to encode as Σ-types, actual simplices and
their faces/skeletons which are given by tuples (x⃑ : A₀, ...) inhabiting
those shapes, and *positions* which are functions mapping simplices/skeleta to
faces.

Increasing subsequences α of the sequence /0/1/.../n/ correspond to positions of
faces of Δⁿ. There should then be a function `face` taking an n-simplex and such
a subsequence α and returning the corresponding face.
-}

data Subseq (n : ℕ) : {l : ℕ} → Type₀
hd : ∀ {n l} ⦃ nz : O < l ⦄ → Subseq n {l} → ℕ

infixr 30 _/_
infixl 40 _/
data Subseq n where
  _/  : ℕ → Subseq n {S O}
  _/_ : ∀ {l} ⦃ nz : O < l ⦄
      → (x : ℕ) (s : Subseq n {l})
      → ⦃ lt : x < (hd ⦃ nz ⦄ s) ⦄
      → Subseq n {S l}

hd (x /) = x
hd (x / xs) = x

seqr : (m n : ℕ) → Subseq n
seqr O n = {!!}
seqr (S m) n = {!!}


{- Semisimplicial types -}
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
  X     : (i n : ℕ) ⦃ h : i ≤ n ⦄ → Ty (SST n)
  A     : (i n : ℕ) ⦃ h : i ≤ n ⦄ → Tm (X i n)
  sk    : (k n : ℕ) ⦃ nz : O < n ⦄ ⦃ lt : k < n ⦄ → Ty (SST₋ n)
  face  : {k n : ℕ} → {!!}

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
    XO-coercion : ∀ {n} → Coerceable (Tm (X O n [ p ])) (Tm U)
    coerce ⦃ XO-coercion {n} ⦄ = tr Tm (ap _[ p ] (XO=U n) ∙ U-[])

  A O O = ν
  A O (S n) = A O n [ p ]ₜ
  A (S i) (S n) ⦃ inr x ⦄ = A (S i) n ⦃ S<S-dec-r x ⦄ [ p ]ₜ
  A (S i) (S n) ⦃ inl _ ⦄ = ν

  sk O (S O) =
    el (A O O ↗) ̂× el (A O O ↗)
  sk O (S (S n)) =
    sk O (S n) [ p ] ̂× el (coerce ⦃ XO-coercion {n} ⦄ (A O (S n)))
  sk (S k) (S n) ⦃ nz ⦄ ⦃ lt ⦄ =
    ̂Σ (sk k (S n) ⦃ nz ⦄ ⦃ <-dec-l lt ⦄)
      {!A_k (correct tuple)!}

  face = {!!}
