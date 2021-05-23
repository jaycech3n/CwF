{-# OPTIONS --without-K #-}

module Face3 where

open import Arith

{- Faces of Δⁿ -}

-- Face n k is the type of faces of Δⁿ of length k (i.e. dim (k-1))
data Face : (n k : ℕ) {l : ℕ} → Type₀ where
  ff  : {n : ℕ} (k : ℕ) → Face n k {k}
  ext : {n k : ℕ}
        (i : ℕ) ⦃ e : i ≤ n ⦄
        {l : ℕ} → Face n k {l} → ⦃ e' : l < i ⦄
        → Face n (S k) {i}


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


Face-k≤l : ∀ {n k l} → Face n k {l} → k ≤ l
Face-k≤l (ff _) = inl idp
Face-k≤l (ext _ f ⦃ e' ⦄) = <-S≤ (≤-<-< (Face-k≤l f) e')


{- We want to define the colexicographic predecessor function on Face n k. In
order to do this we need a function giving the (co)lexicographically last
length-k face of Δⁿ ending in a given vertex. For example, we want

  last n 0 i = ff 0         : Face n 0 {0}
  last n 1 0 = ff 1         : Face n 1 {1}
  last n 1 i = ext i (ff 0) : Face n 1 {i}    for i = 1, ..., n

and in general,

  last n (S (S k)) (S k) = ff (S (S k)) : Face n (S (S k)) {S (S k)}
  last n (S (S k)) (S i) =
    ext (S i) (last n (S k) i) : Face n (S (S k)) {S i}
    for i = k+1, ..., n

As we can see, there are some technical details to do with the type of this
function. -}

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

l-of-pred : ∀ {n k l} → Face n k {l} → ℕ
l-of-pred (ff k) = k
l-of-pred (ext (S i) (ff _)) = i
l-of-pred (ext (S i) (ext _ _)) = S i

l-of-pred-≤-l : ∀ {n k l} (f : Face n k {l}) → l-of-pred f ≤ l
l-of-pred-≤-l (ff _) = inl idp
l-of-pred-≤-l (ext (S i) (ff _)) = lteS
l-of-pred-≤-l (ext (S i) (ext _ _)) = inl idp

pred : ∀ {n k l} ⦃ h : k ≤ l ⦄ (f : Face n k {l}) → Face n k {l-of-pred f}
pred {n} {k} {.k} ⦃ h ⦄ (ff .k) = ff k
pred {n} {S k} {.(S i)} ⦃ h ⦄ (ext (S i) ⦃ e ⦄ (ff _)) =
  last i ⦃ S≤-≤ e ⦄ ⦃ {!--neither h nor e' work here; Agda needs something of the form `inr _` to be able to typecheck!} ⦄
pred {n} {S (S k)} {.(S j)} ⦃ h ⦄ (ext (S j) (ext i f) ⦃ e' ⦄) =
  ext (S j) (pred ⦃ Face-k≤l (ext i f) ⦄ (ext i f)) ⦃ ≤-<-< (l-of-pred-≤-l (ext i f)) e' ⦄
-- pred (ff k) = ff k
-- pred {n} {S k} (ext (S i) ⦃ e ⦄ (ff _) ⦃ e' ⦄) = {!!}
-- pred (ext (S j) (ext i f) ⦃ e' ⦄) =
--   ext (S j) (pred (ext i f)) ⦃ ≤-<-< (l-of-pred-≤-l (ext i f)) e' ⦄
