{-# OPTIONS --without-K #-}

module Face where

open import Arith

{- Faces of Δⁿ -}

-- Face n k is the type of faces of Δⁿ of length k (i.e. dim (k-1))
data Face : (n k : ℕ) {l : ℕ} → Type₀ where
  ff  : {n : ℕ} (k : ℕ) → Face n k {k}
  ext : {n k : ℕ}
        (i : ℕ) ⦃ e : i ≤ n ⦄
        {l : ℕ} → Face n k {l} → ⦃ e' : l < i ⦄
        → Face n (S k) {i}

Face-k≤l : ∀ {n k l} → Face n k {l} → k ≤ l
Face-k≤l (ff _) = inl idp
Face-k≤l (ext _ f ⦃ e' ⦄) = <-S≤ (≤-<-< (Face-k≤l f) e')


-- Example
private
  example : Face 4 _
  example =
    -- ff 0 -- *

    -- ff 1         -- 0
    -- ext 1 (ff 0) -- 1
    -- ext 2 (ff 0) -- 2
    -- ext 3 (ff 0) -- 3
    -- ext 4 (ff 0) -- 4

    -- ff 2                 -- 01
    -- ext 2 (ff 1)         -- 02
    -- ext 2 (ext 1 (ff 0)) -- 12
    -- ext 3 (ff 1)         -- 03
    -- ext 3 (ext 1 (ff 0)) -- 13
    -- ext 3 (ext 2 (ff 0)) -- 23
    -- ext 4 (ff 1)         -- 04
    -- ext 4 (ext 1 (ff 0)) -- 14
    -- ext 4 (ext 2 (ff 0)) -- 24
    -- ext 4 (ext 3 (ff 0)) -- 34

    -- ff 3                         -- 012
    -- ext 3 (ff 2)                 -- 013
    -- ext 3 (ext 2 (ff 1))         -- 023
    -- ext 3 (ext 2 (ext 1 (ff 0))) -- 123
    -- ext 4 (ff 2)                 -- 014
    -- ext 4 (ext 2 (ff 1))         -- 024
    -- ext 4 (ext 2 (ext 1 (ff 0))) -- 124
    -- ext 4 (ext 3 (ff 1))         -- 034
    -- ext 4 (ext 3 (ext 1 (ff 0))) -- 134
    -- ext 4 (ext 3 (ext 2 (ff 0))) -- 234

    -- ff 4                              -- 0123
    -- ext 4 (ff 3)                      -- 0124
    -- ext 4 (ext 3 (ff 2))              -- 0134
    -- ext 4 (ext 3 (ext 2 (ff 1)))      -- 0234
    ext 4 (ext 3 (ext 2 (ext 1 (ff 0)))) -- 1234


{- We want to define the colexicographic predecessor function on Face n k. In
order to do this we need a function giving the (co)lexicographically last
length-k face of Δⁿ ending in a given vertex. There are some technical details
to do with the type of this function. -}

l-of-last : (k i : ℕ) ⦃ h : k ≤ S i ⦄ → ℕ
l-of-last O i = O
l-of-last (S k) i ⦃ inl _ ⦄ = S k
l-of-last (S k) i ⦃ inr _ ⦄ = i

last : ∀ {n k} (i : ℕ) ⦃ e : i ≤ n ⦄ ⦃ h : k ≤ S i ⦄ → Face n k {l-of-last k i}
last {n} {O}   i ⦃ h ⦄ = ff O
last {n} {S k} i ⦃ h = inl _ ⦄ = ff (S k)
last {n} {S k} O ⦃ h = inr (ltSR ()) ⦄
last {n} {S k} (S i) ⦃ e ⦄ ⦃ inr x ⦄ =
  ext (S i) (last i ⦃ S≤-≤ e ⦄ ⦃ inr (<-cancel-S x) ⦄) ⦃ l-of-last-< x ⦄
  where
  l-of-last-< : ∀ {k i} (x : S k < S (S i))
                → l-of-last k i ⦃ inr (<-cancel-S {k} {S i} x) ⦄ < S i
  l-of-last-< {O} {i} x = O<S i
  l-of-last-< {S k} {i} x = ltS

l-of-pred : ∀ {n k l} ⦃ h : k ≤ l ⦄ → Face n k {l} → ℕ
l-of-pred (ff k) = k
l-of-pred (ext i (ext _ f)) = i
l-of-pred ⦃ h = inl x ⦄ (ext i (ff _)) = i
l-of-pred ⦃ h = inr x ⦄ (ext (S i) (ff _)) = i

l-of-pred-≤l : ∀ {n k l} ⦃ h : k ≤ l ⦄ (f : Face n k {l}) → l-of-pred f ≤ l
l-of-pred-≤l (ff _) = inl idp
l-of-pred-≤l (ext _ (ext _ f)) = inl idp
l-of-pred-≤l ⦃ h = inl x ⦄ (ext _ (ff _)) = inl idp
l-of-pred-≤l ⦃ h = inr x ⦄ (ext (S i) (ff _)) = inr ltS

pred : ∀ {n k l} ⦃ h : k ≤ l ⦄ (f : Face n k {l}) → Face n k {l-of-pred f}
pred (ff _) = ff _ -- dummy; never actually take the predecessor of first (k-1)-face
pred (ext (S j) (ext i f) ⦃ e' ⦄) =
  ext (S j) (pred ⦃ Sk≤i ⦄ (ext i f)) ⦃ ≤-<-< (l-of-pred-≤l ⦃ Sk≤i ⦄ (ext i f)) e' ⦄
  where
  Sk≤i = Face-k≤l (ext i f)
pred {n} {S k} ⦃ h = inl p ⦄ (ext (S i) (ff _)) =
  tr (λ l → Face n (S k) {l}) p (ff (S k))
pred ⦃ h = inr x ⦄ (ext (S i) ⦃ e ⦄ (ff _) ⦃ e' ⦄) = last i ⦃ S≤-≤ e ⦄ ⦃ inr x ⦄
