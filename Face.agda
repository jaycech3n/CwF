{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Face where

open import Arith

-- k-faces of Δⁿ. i is the "last vertex" of the face.
data Face : (n k i : ℕ) → Type₀ where
  -- Zeroth vertex of Δⁿ
  vtx : {n : ℕ} → Face n O O
  -- Next k-face in lexicographic order
  nxt : {n k i : ℕ} (f : Face n k i) ⦃ e : i < n ⦄ → Face n k (S i)
  -- Extend k-face to (k+1)-face
  ext : {n k i : ℕ} ⦃ e : k < n ⦄ ⦃ e' : i < n ⦄
        (f : Face n k i) → Face n (S k) (S i)

last-face : (n k : ℕ) ⦃ k≤n : k ≤ n ⦄ → Face n k n
last-face = {!!}
