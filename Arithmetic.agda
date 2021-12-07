{-# OPTIONS --without-K #-}

module Arithmetic where

open import Prelude public

-- We use instances for rudimentary automatic solving of certain inequality
-- constraints.

instance
  O≤-inst : ∀ {n} → O ≤ n
  O≤-inst {n} = O≤ n

instance
  O<-inst : ∀ {n} → O < 1+ n
  O<-inst {n} = O<S n

{-
instance
  S<S-inst : {m n : ℕ} ⦃ m<n : m < n ⦄ → 1+ m < 1+ n
  S<S-inst ⦃ m<n ⦄ = <-ap-S m<n

instance
  solve-S≤S : {m n : ℕ} ⦃ h : m ≤ n ⦄ → 1+ m ≤ 1+ n
  solve-S≤S ⦃ h ⦄ = ≤-ap-S h
-}

O+O : ∀ {m n} → m == O → n == O → m + n == O
O+O {m} {n} p q =
  m + n =⟨ p |in-ctx (_+ n) ⟩
  O + n =⟨ q |in-ctx (O +_) ⟩
  O =∎

+==O-r : ∀ {m n} → m + n == O → n == O
+==O-r {m = O} p = p
+==O-r {m = 1+ m} {n} p = ⊥-elim (ℕ-S≠O (m + n) p)

O<→O<+r : ∀ {m n} → O < m → O < m + n
O<→O<+r {1+ m} {n} x = O<S (m + n)

<1→=O : ∀ x → x < 1 → x == O
<1→=O O _ = idp
<1→=O (1+ x) (ltSR ())

<S→≤ : ∀ {m n} →  m < 1+ n → m ≤ n
<S→≤ ltS = lteE
<S→≤ (ltSR m<n) = inr m<n

<→S≤ : ∀ {m n} → m < n → 1+ m ≤ n
<→S≤ ltS = lteE
<→S≤ (ltSR m<n) = inr (<-ap-S m<n)

S≤→< : ∀ {m n} → 1+ m ≤ n → m < n
S≤→< {m} (inl Sm==n) = tr (m <_) Sm==n ltS
S≤→< (inr Sm<n) = <-trans ltS Sm<n

≤→<S : ∀ {m n} → m ≤ n → m < 1+ n
≤→<S {m} (inl m==n) = tr (λ □ → m < 1+ □) m==n ltS
≤→<S (inr m<n) = ltSR m<n

S≤→≤ : ∀ {m n} → 1+ m ≤ n → m ≤ n
S≤→≤ h = ≤-trans lteS h

≤→<→< : ∀ {k m n} → k ≤ m → m < n → k < n
≤→<→< {k} {m} {n} (inl p) h = tr (_< n) (! p) h
≤→<→< (inr e) h = <-trans e h

¬-< : ∀ {n} → n < n → ⊥
¬-< id< = <-to-≠ id< idp

≤→≠→< : ∀ {m n} → m ≤ n → m ≠ n → m < n
≤→≠→< (inl u) v = ⊥-elim (v u)
≤→≠→< (inr u) _ = u

≠O→O< : ∀ {n} → n ≠ O → O < n
≠O→O< {O}    u = ⊥-elim (u idp)
≠O→O< {1+ n} _ = O<S n

=-cancel-S : ∀ {m n} → 1+ m == 1+ n :> ℕ → m == n
=-cancel-S idp = idp

<→ℕ-pred< : ∀ {k} n → O < n → n ≤ k → ℕ-pred n < k
<→ℕ-pred< (1+ n) _ Sn≤k = S≤→< Sn≤k

{-
module _ {m n : ℕ} where
  ==-cancel-S : _==_ {A = ℕ} (1+ m) (1+ n) → m == n
  ==-cancel-S idp = idp

  S<-< : 1+ m < n → m < n
  S<-< h = <-trans ltS h

  S<-≤ : 1+ m < n → m ≤ n
  S<-≤ h = inr (S<-< h)

  S≤-< : 1+ m ≤ n → m < n
  S≤-< (inl x) = tr (_ <_) x ltS
  S≤-< (inr x) = <-trans ltS x

  <-S≤ : m < n → 1+ m ≤ n
  <-S≤ ltS = inl idp
  <-S≤ (ltSR x) = inr (<-ap-S x)

+==O-l : {m n : ℕ} → m + n == O → m == O
+==O-l {m = O} _ = idp
-}


{- Trichotomy -}

ℕ-trichotomy' : (m n : ℕ) → (m ≤ n) ⊔ (n < m)
ℕ-trichotomy' m n with ℕ-trichotomy m n
... | inl m=n = inl (inl m=n)
... | inr (inl m<n) = inl (inr m<n)
... | inr (inr n<m) = inr n<m


{- ℕ₊ -}

ℕ₊ : Type₀
ℕ₊ = Σ[ n ∈ ℕ ] O < n

instance
  ℕ₊-reader : FromNat ℕ₊
  FromNat.in-range ℕ₊-reader n = O < n
  FromNat.read ℕ₊-reader n ⦃ O<n ⦄ = n , O<n


{- Monus -}

infix 80 _∸_
_∸_ : ℕ → ℕ → ℕ
O ∸ n = O
1+ m ∸ O = 1+ m
1+ m ∸ 1+ n = m ∸ n

∸-move-S-l : ∀ {k} m n → m ∸ n == 1+ k → m ∸ 1+ n == k
∸-move-S-l (1+ m) (1+ n) p = ∸-move-S-l m n p
∸-move-S-l (1+ O) O p = =-cancel-S p
∸-move-S-l (2+ m) O p = =-cancel-S p

∸→≤ : ∀ {m n} → m ∸ n == 0 → m ≤ n
∸→≤ {O} {n} _ = O≤ n
∸→≤ {1+ m} {1+ n} p = ≤-ap-S (∸→≤ p)

∸→< : ∀ {m n k} → m ∸ n == 1+ k → n < m
∸→< {1+ m} {O} _ = O<S m
∸→< {1+ m} {1+ n} p = <-ap-S (∸→< p)


{- Binomial coefficients -}

binom : ℕ → ℕ → ℕ
binom    n      O   = 1
binom    O   (1+ k) = 0
binom (1+ n) (1+ k) = binom n k + binom n (1+ k)

binom==O-n-rec : ∀ {n} k
                 → binom (1+ n) k == O
                 → binom    n   k == O
binom==O-n-rec (1+ k) p = +==O-r p

binom==O-k-rec : ∀ {k} n
                 → binom n    k   == O
                 → binom n (1+ k) == O
binom==O-k-rec O _ = idp
binom==O-k-rec {k} (1+ n) p =
  O+O (binom==O-n-rec k p) (binom==O-k-rec n (binom==O-n-rec k p))

binom-n-Sn : ∀ n → binom n (1+ n) == O
binom-n-Sn O = idp
binom-n-Sn (1+ n) = O+O (binom-n-Sn n) (binom==O-k-rec n (binom-n-Sn n))

binom-n-n : ∀ n → binom n n == 1
binom-n-n O = idp
binom-n-n (1+ n) =
  (binom n n) + binom n (1+ n) =⟨ binom-n-Sn n |in-ctx (binom n n +_) ⟩
  (binom n n) + O              =⟨ +-comm _ O ∙ binom-n-n n ⟩
  1 =∎

binom-n-1 : ∀ n → binom n 1 == n
binom-n-1 O = idp
binom-n-1 (1+ n) = ap 1+ (binom-n-1 n)

binom-Sn-n : ∀ n → binom (1+ n) n == 1+ n
binom-Sn-n O = idp
binom-Sn-n (1+ n) =
  binom (1+ n) n + (binom n n + binom n (1+ n))
  =⟨ ap (λ □ →   □  + (binom n n + binom n (1+ n))) (binom-Sn-n n)
   ∙ ap (λ □ → 1+ n + (     □    + binom n (1+ n))) (binom-n-n n)
   ∙ ap (λ □ → 1+ n + (     1    +        □      )) (binom-n-Sn n)
   ⟩
    1+ n + (1 + O)
  =⟨ +-comm (1+ n) (1 + O) ⟩
  1+ (1+ n)
  =∎

Sn≤binom-Sn-n : ∀ n → 1+ n ≤ binom (1+ n) n
Sn≤binom-Sn-n n = inl (! (binom-Sn-n n))

binom>O : ∀ m n → n ≤ m → O < binom m n
binom>O _      O      _        = ltS
binom>O O      (1+ n) (inl ())
binom>O (1+ m) (1+ n) Sn≤Sm    = O<→O<+r (binom>O m n (≤-cancel-S Sn≤Sm))

binom≥1 : ∀ m n → n ≤ m → 1 ≤ binom m n
binom≥1 m n = <→S≤ ∘ binom>O m n
