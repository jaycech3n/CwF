module Sieves where

open import Arithmetic public
open import Fin public

-- A sieve (n,k,t) describes the shape of partial k-skeleta of n-simplices in
-- which the first t k-faces are present.

is-presieve : ℕ → ℕ → ℕ → Type₀
is-presieve n k t = (k < n) × (t ≤ binom (1+ n) (1+ k))

is-sieve : ℕ → ℕ → (t : ℕ) ⦃ tpos : O < t ⦄ → Type₀
is-sieve n k t = is-presieve n k t

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

Sieve : Type₀
Sieve = Σ[ s ∈ (ℕ × ℕ × ℕ) ]
          let n = fst s
              k = 2nd s
              t = 3rd s
          in (O < t) × (k < n) × (t ≤ binom (1+ n) (1+ k))

get-n get-k get-t : Sieve → ℕ
get-n ((n , k , t) , _) = n
get-k ((n , k , t) , _) = k
get-t ((n , k , t) , _) = t


{- Face maps -}

is-increasing : ∀ {m n} → (Fin m → Fin n) → Type₀
is-increasing f = ∀ {i j} → fst i < fst j → fst (f i) < fst (f j)

_→+_ : ℕ → ℕ → Type₀
m →+ n = Σ (Fin (1+ m) → Fin (1+ n)) is-increasing

fun-of : ∀ {m n} → (m →+ n) → Fin (1+ m) → Fin (1+ n)
fun-of (f , _) = f

_→+-⊆_ : ∀ {m m' n} (f : m →+ n) (g : m' →+ n) → Type₀
_→+-⊆_ {m} f g = (i : Fin (1+ m)) → hfiber (fun-of g) (fun-of f i)

_→+-⊆?_ : ∀ {m m' n} (f : m →+ n) (g : m' →+ n) → Dec (f →+-⊆ g)
_→+-⊆?_ f g = ∀-Fin? _ (λ i → Fin-hfiber-dec (fun-of g) (fun-of f i))


{- Subsieves -}

-- This calculates the shape of the intersection of a face map f with
-- the presieve (n,k,t).

pre[_,_,_]∩_ : (n k t : ℕ)
            → {m : ℕ} (f : m →+ n)
            → is-presieve n k t
            → Maybe Sieve
(pre[ n , O ,   O  ]∩ f) iPS = none
(pre[ n , O , 1+ t ]∩ f) iPS = {!Maybe-case!}
(pre[ n , 1+ k , t ]∩ f) iPS = {!!}
