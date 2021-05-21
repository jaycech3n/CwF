{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Face2 where

open import Arith

{- k-faces of Δⁿ -}

-- Face n k is the type of faces of Δⁿ of length k (i.e. dimension (k-1)). z is
-- a guard condition.
data Face : {has-prev : Bool} {z : ℕ} (n k : ℕ) → Type₀ where
  ff  : ∀ {n} (k : ℕ) → Face {false} {k} n k -- ff k is the first face of length k
  ext : (i : ℕ) {z n k : ℕ} ⦃ e : i ≤ n ⦄ ⦃ e' : z < i ⦄
        → ∀ {has-prev} → Face {has-prev} {z} n k
        → Face {true} {i} n (S k)

* : ∀ {n} → Face n O
* = ff O


-- Example
private
  ff+ : ∀ {n} (k : ℕ) → Face n (S k)
  ff+ n = ff (S n)

  syntax ff+ n = 0→ n

  example : Face 4 _
  example =
    -- *

    -- 0→ 0    -- 0
    -- ext 1 * -- 1
    -- ext 2 * -- 2
    -- ext 3 * -- 3
    -- ext 4 * -- 4

    -- 0→ 1            -- 01
    -- ext 2 (0→ 0)    -- 02
    -- ext 2 (ext 1 *) -- 12
    -- ext 3 (0→ 0)    -- 03
    -- ext 3 (ext 1 *) -- 13
    -- ext 3 (ext 2 *) -- 23
    -- ext 4 (0→ 0)    -- 04
    -- ext 4 (ext 1 *) -- 14
    -- ext 4 (ext 2 *) -- 24
    -- ext 4 (ext 3 *) -- 34

    -- 0→ 2                    -- 012
    -- ext 3 (0→ 1)            -- 013
    -- ext 3 (ext 2 (0→ 0))    -- 023
    -- ext 3 (ext 2 (ext 1 *)) -- 123
    -- ext 4 (0→ 1)            -- 014
    -- ext 4 (ext 2 (0→ 0))    -- 024
    -- ext 4 (ext 2 (ext 1 *)) -- 124
    -- ext 4 (ext 3 (0→ 0))    -- 034
    -- ext 4 (ext 3 (ext 1 *)) -- 134
    -- ext 4 (ext 3 (ext 2 *)) -- 234

    -- 0→ 3                         -- 0123
    -- ext 4 (0→ 2)                 -- 0124
    -- ext 4 (ext 3 (0→ 1))         -- 0134
    -- ext 4 (ext 3 (ext 2 (0→ 0))) -- 0234
    ext 4 (ext 3 (ext 2 (ext 1 *))) -- 1234


-- (Co)lexicographically last k-face of Δⁿ ending in i
-- last-face : ...

-- Colexicographic predecessor (of length k)
prev-face : ∀ {z} (n k : ℕ)
            → Face {has-prev = true} {z} n k
            → Σ Bool (λ has-prev → Σ ℕ (λ y → Face {has-prev} {y} n k))
prev-face n .(S _) (ext (S i) (ff _)) = {!!}
prev-face n .(S (S _)) (ext j (ext i x)) = _ , _ ,
  ext j ⦃ e' = {!!} ⦄ (snd (snd (prev-face _ _ (ext i x))))
