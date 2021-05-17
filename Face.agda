{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Face where

open import Arith

{- k-faces of Δⁿ -

The set of face maps {f : [k] → [n] | k ≤ n} may be formed by inductive
application of the following three operations:
  1. f : [0] → [n] is the zeroth vertex.
  2. f : [k] → [n] is of the form [v₀, ... , vₖ₋₁, vₖ + 1] for some face
     [v₀, ... , vₖ₋₁, vₖ] ("next" face).
  3. f : [k+1] → [n] is of the form [v₀, ... , vₖ, vₖ + 1] for some face
     [v₀, ... , vₖ₋₁, vₖ] ("extension" of a face). -}

data Face : (n k i : ℕ) → Type₀ where
  vtx : {n : ℕ} → Face n O O
  nxt : {n k i : ℕ} (f : Face n k i) ⦃ e : i < n ⦄ → Face n k (S i)
  ext : {n k i : ℕ} ⦃ e : k < n ⦄ ⦃ e' : i < n ⦄
        (f : Face n k i) → Face n (S k) (S i)

last-face : (n k : ℕ) ⦃ k≤n : k ≤ n ⦄ → Face n k n
last-face = {!!}
