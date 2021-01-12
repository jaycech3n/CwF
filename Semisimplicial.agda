{-# OPTIONS --without-K #-}

{--- Semisimplicial types in internal CwFs---}

module Semisimplicial where

open import CwF
open import Sieves

{- The combinatorics of faces

`coords k n` gives the k-faces of Δⁿ for 0 ≤ i ≤ k. The returned list is
organized in blocks by dimension. A k-face is given by a sequence of k+1 points.
-}

coords : (k n : ℕ) ⦃ lt : k < n ⦄ ⦃ nz : O < n ⦄ → List (List Seq)
coords O n = Seq+ (S O) O n :: nil
coords (S k) n ⦃ lt ⦄ = snoc (coords k n ⦃ <-dec-l lt ⦄) (Seq+ (S (S k)) O n)

face-coords : (k n : ℕ) ⦃ lt : k < n ⦄ ⦃ nz : O < n ⦄ → Seq → List (List Bool)
face-coords k n cs = map (map (_⊂ cs)) (coords k n)

{- Semisimplicial types -}

module _ {i} (C : WildCategory {i}) (cwF : WildCwFStructure C)
  (piStr : PiStructure cwF) (sigmaStr : SigmaStructure cwF)
  (uStr : UStructure cwF)
  where
  open WildCwFStructure cwF
  open PiStructure piStr
  open SigmaStructure sigmaStr
  open UStructure uStr

  {- Mutually define: -}

  SST  : ℕ → Con
  SST₋ : ℕ → Con
  X    : (i n : ℕ) ⦃ le : i ≤ n ⦄ → Ty (SST n)
  A    : (i n : ℕ) ⦃ le : i ≤ n ⦄ → Tm (X i n)
  sk   : (k n : ℕ) ⦃ lt : k < n ⦄ ⦃ nz : O < n ⦄ → Ty (SST₋ n)
  {-
  `face k n cs ν` picks out the subtuple of `ν : sk k n [ p ]` corresponding to
  the cs-th k-subface and all its subfaces.
  -}
  face : (k n : ℕ) ⦃ lt : k < n ⦄ ⦃ nz : O < n ⦄
       → Seq → Tm (sk k n [ p ]) → {!!}

  SST₋ O = ◆
  SST₋ (S n) = SST n

  SST O = ◆ ∷ U
  SST (S n) = SST n ∷ (sk n (S n) ̂→ U)

  X O O = U [ p ]
  X O (S n) = X O n [ p ]
  X (S i) (S n) ⦃ inr x ⦄ = X (S i) n ⦃ S<S-dec-r x ⦄ [ p ] -- i < n
  X (S i) (S n) ⦃ inl _ ⦄ = (sk n (S n) ̂→ U)[ p ] -- i = n

  XO=U : (n : ℕ) → X O n == U
  XO=U O     = U-[]
  XO=U (S n) = X O n [ p ]
             =⟨ XO=U n |in-ctx _[ p ] ⟩ U [ p ]
             =⟨ U-[] ⟩ U =∎

  private
    module coercions where
      instance
        XO-coercion : ∀ {n} → Coerceable (Tm (X O n)) (Tm U)
        coerce ⦃ XO-coercion {n} ⦄ = tr Tm (XO=U n)

  open coercions

  A O O = ν
  A O (S n) = A O n [ p ]ₜ
  A (S i) (S n) ⦃ inr x ⦄ = A (S i) n ⦃ S<S-dec-r x ⦄ [ p ]ₜ
  A (S i) (S n) ⦃ inl _ ⦄ = ν

  face k n cs ν = {!!}

  sk O (S n) = el (coerce ⦃ XO-coercion {n} ⦄ (A O n)) ˣ S (S n)
  sk (S k) (S n) ⦃ lt ⦄ ⦃ nz ⦄
    = ̂Σ (sk k (S n) ⦃ <-dec-l lt ⦄ ⦃ nz ⦄)
        {!(A (S k) n ⦃ S<S-dec-r lt ⦄ [ p ]ₜ) ` ?!}
