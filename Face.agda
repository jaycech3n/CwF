{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Face where

open import Arith

data Face : (n k i : ℕ) → Type₀ where -- i is the "last vertex" of the face
  -- Vertex of Δⁿ
  vtx : {n : ℕ} (i : ℕ) ⦃ e : i ≤ n ⦄ → Face n O i
  -- Extend k-face to (k+1)-face
  ext : {n k i : ℕ} ⦃ e : k < n ⦄ ⦃ e' : i < n ⦄
        (f : Face n k i) → Face n (S k) (S i)
  -- Next k-face in lexicographic order
  nxt : {n k i : ℕ} (f : Face n k i) ⦃ e : i < n ⦄ → Face n k (S i)

last-face : (n k : ℕ) ⦃ k≤n : k ≤ n ⦄ → Face n k n
last-face = {!!}
