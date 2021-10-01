{-# OPTIONS --without-K #-}

module Sieves where

open import Arithmetic public
open import Fin public

-- A sieve (n,k,t) describes the shape of partial k-skeleta of n-simplices in
-- which the first t > 0 k-faces are present. Presieves are sieves where t ≥ 0.

is-presieve : ℕ → ℕ → ℕ → Type₀
is-presieve n k t = (k < n) × (t ≤ binom (1+ n) (1+ k))

prev-is-presieve-t : {n k t : ℕ} → is-presieve n k (1+ t) → is-presieve n k t
prev-is-presieve-t (k<n , St≤binom) = k<n , (≤-trans lteS St≤binom)

Presieve : ℕ → ℕ → Type₀
Presieve n k = Σ[ t ∈ ℕ ] is-presieve n k t

get-t : ∀ {n k} → Presieve n k → ℕ
get-t = fst

is-sieve : ℕ → ℕ → (t : ℕ) ⦃ tpos : O < t ⦄ → Type₀
is-sieve n k t = is-presieve n k t

prev-is-sieve-t : {n k t : ℕ} ⦃ tpos : O < t ⦄
                  → is-sieve n k (1+ t)
                  → is-sieve n k t
prev-is-sieve-t = prev-is-presieve-t

prev-is-sieve-k : {n k : ℕ} (iS@(Sk<n , _) : is-sieve n (1+ k) 1)
                  → is-sieve n k (binom (1+ n) (1+ k))
                             ⦃ binom>O (1+ n) (1+ k) (ltSR Sk<n) ⦄
prev-is-sieve-k (Sk<n , 1≤binom) = <-trans ltS Sk<n , inl idp

is-last-sieve : (n : ℕ) → is-sieve (1+ n) n (2+ n)
is-last-sieve n = ltS , Sn≤binom-Sn-n (1+ n)

Sieve : ℕ → ℕ → Type₀
Sieve n k = Σ[ t ∈ ℕ ] (O < t) × is-presieve n k t

pre-of-sieve : ∀ {n k} → Sieve n k → Presieve n k
pre-of-sieve (t , _ , iPS) = t , iPS

next-sieve-t : ∀ {n k} t → k < n → t < binom (1+ n) (1+ k) → Sieve n k
next-sieve-t t k<n t<binom = 1+ t , O<S t , k<n , <→S≤ t<binom


{- Face maps -}

is-increasing : ∀ {m n} → (Fin m → Fin n) → Type₀
is-increasing f = ∀ {i j} → fst i < fst j → fst (f i) < fst (f j)

_→+_ : ℕ → ℕ → Type₀
m →+ n = Σ (Fin (1+ m) → Fin (1+ n)) is-increasing

fun-of : ∀ {m n} → (m →+ n) → Fin (1+ m) → Fin (1+ n)
fun-of (f , _) = f

_img-⊆_ : ∀ {m m' n} (f : m →+ n) (g : m' →+ n) → Type₀
_img-⊆_ {m} f g = (i : Fin (1+ m)) → hfiber (fun-of g) (fun-of f i)

_img-⊆?_ : ∀ {m m' n} (f : m →+ n) (g : m' →+ n) → Dec (f img-⊆ g)
_img-⊆?_ f g = ∀-Fin? _ (λ i → Fin-hfiber-dec (fun-of g) (fun-of f i))

map-of-index : (n k t : ℕ) ⦃ tpos : O < t ⦄ → is-sieve n k t → (k →+ n)
map-of-index n k t = {!!}


{- Subsieves -}

-- (pre[ n , k , t ]∩ f) calculates the shape of the intersection of a
-- face map f with the presieve (n, k, t).

pre[_,_,_]∩_ : (n k t : ℕ)
               → {m : ℕ} (f : m →+ n)
               → is-presieve n k t
               → Presieve n k

t-of-∩ : (n k t : ℕ) {m : ℕ} (f : m →+ n) (iPS : is-presieve n k t)
         → get-t ((pre[ n , k , t ]∩ f) iPS) ≤ t

(pre[ n , O , O ]∩ f) iPS = O , iPS

(pre[ n , O , 1+ t ]∩ f) iPS@(_ , St≤binom)
  with (pre[ n , O , t ]∩ f) (prev-is-presieve-t iPS)
     | t-of-∩ n O t f (prev-is-presieve-t iPS)
     | (map-of-index n O (1+ t) iPS) img-⊆? f
...  | t' , O<n , _ | t'≤t | inl _
     = pre-of-sieve (next-sieve-t t' O<n (S≤→< (≤-trans (≤-ap-S t'≤t) St≤binom)))
...  | s            | _    | inr _
     = s

(pre[ n , 1+ k , t ]∩ f) iPS = {!!}

t-of-∩ n O O f iPS = inl idp

t-of-∩ n O (1+ t) f iPS
  with (pre[ n , O , t ]∩ f) (prev-is-presieve-t iPS)
     | t-of-∩ n O t f (prev-is-presieve-t iPS)
     | (map-of-index n O (1+ t) iPS) img-⊆? f
...  | t' , _ | t'≤t | inl _ = ≤-ap-S t'≤t
...  | t' , _ | t'≤t | inr _ = lteSR t'≤t

t-of-∩ n (1+ k) t f iPS = {!!}
