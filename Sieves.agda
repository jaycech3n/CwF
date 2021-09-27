module Sieves where

open import Arithmetic public

-- A sieve (n,k,t) describes the shape of partial k-skeleta of n-simplices in
-- which the first t k-faces are present.

is-sieve : ℕ → ℕ → (t : ℕ) ⦃ tpos : O < t ⦄ → Type₀
is-sieve n k t = (k < n) × (t ≤ binom (1+ n) (1+ k))

Sieve = Σ (ℕ × ℕ) λ{ (n , k) → Σ ℕ  (λ t → ⦃ tpos : O < t ⦄ → is-sieve n k t) }

get-n get-k get-t : Sieve → ℕ
get-n ((n , k) , (t , _)) = n
get-k ((n , k) , (t , _)) = k
get-t ((n , k) , (t , _)) = t

is-last-sieve : (n : ℕ) → is-sieve (1+ n) n (2+ n)
is-last-sieve n = ltS , Sn≤binom-Sn-n (1+ n)

prev-is-sieve-t : {n k t : ℕ} ⦃ tpos : O < t ⦄
                  → is-sieve n k (1+ t)
                  → is-sieve n k t
prev-is-sieve-t (k<n , St<binom) = k<n , (≤-trans lteS St<binom)

prev-is-sieve-k : {n k : ℕ} (iS@(Sk<n , _) : is-sieve n (1+ k) 1)
                  → is-sieve n k (binom (1+ n) (1+ k))
                             ⦃ binom>O (1+ n) (1+ k) (<-trans Sk<n ltS) ⦄
prev-is-sieve-k (Sk<n , 1≤binom) = <-trans ltS Sk<n , inl idp


{- Face maps -}

is-increasing : ∀ {m n} → (Fin m → Fin n) → Type₀
is-increasing f = ∀ {i j} → fst i < fst j → fst (f i) < fst (f j)

_→+_ : ℕ → ℕ → Type₀
m →+ n = Σ (Fin (1+ m) → Fin (1+ n)) is-increasing

Fin→-init : ∀ {m n} → (Fin (1+ m) → Fin n) → Fin m → Fin n
Fin→-init {O} f ()
Fin→-init {1+ m} f = f ∘ Fin-S

→+-init : ∀ {m n} → (1+ m →+ n) → m →+ n
→+-init {m} (f , f-is-inc) = Fin→-init f , f-is-inc

→+-img : ∀ {m n} → (m →+ n) → List (Fin (1+ n))
→+-img {O}         (f , _) = f 0 :: nil
→+-img {1+ m} m→+n@(f , _) = snoc (→+-img (→+-init m→+n)) (f (1+ m , ltS))


{- Subsieves -}
