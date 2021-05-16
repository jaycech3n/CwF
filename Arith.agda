{-# OPTIONS --without-K #-}

module Arith where

open import Prelude public


{- (In)equalities -}

-- Automatically solve inequality conditions
{-
instance
  solve-≤-refl : {n : ℕ} → n ≤ n
  solve-≤-refl = lteE

instance
  solve-n<S : {n : ℕ} → n < S n
  solve-n<S = ltS
-}

instance
  solve-O≤ : {n : ℕ} → O ≤ n
  solve-O≤ {n} = O≤ n

instance
  solve-O<S : {n : ℕ} → O < S n
  solve-O<S {n} = O<S n

instance
  solve-S<S : {m n : ℕ} ⦃ h : m < n ⦄ → S m < S n
  solve-S<S ⦃ h ⦄ = <-ap-S h

instance
  solve-S≤S : {m n : ℕ} ⦃ h : m ≤ n ⦄ → S m ≤ S n
  solve-S≤S ⦃ h ⦄ = ≤-ap-S h

module _ {m n : ℕ} where
  =-cancel-S : _==_ {A = ℕ} (S m) (S n) → m == n
  =-cancel-S idp = idp

  <S-≤ : m < S n → m ≤ n
  <S-≤ ltS = inl idp
  <S-≤ (ltSR x) = inr x

  S<-< : S m < n → m < n
  S<-< h = <-trans ltS h

  S≤-≤ : S m ≤ n → m ≤ n
  S≤-≤ h = ≤-trans lteS h

  S<-≤ : S m < n → m ≤ n
  S<-≤ h = inr (S<-< h)

  S≤-< : S m ≤ n → m < n
  S≤-< (inl x) = tr (_ <_) x ltS
  S≤-< (inr x) = <-trans ltS x

  <-S≤ : m < n → S m ≤ n
  <-S≤ ltS = inl idp
  <-S≤ (ltSR x) = inr (<-ap-S x)

O<+ : {m n : ℕ} → O < m → O < m + n
O<+ {S m} {n} x = O<S (m + n)

ℕ-+=O : {m n : ℕ} → m + n == O → m == O
ℕ-+=O {m = O} _ = idp

ℕ-+=O' : {m n : ℕ} → m + n == O → n == O
ℕ-+=O' {m = O} p = p
ℕ-+=O' {m = S m} {n} p = ex-falso (ℕ-S≠O (m + n) p)

ℕ-O+O : {m n : ℕ} → m == O → n == O → m + n == O
ℕ-O+O {m} {n} p q =
  m + n =⟨ p |in-ctx (_+ n) ⟩
  O + n =⟨ q |in-ctx (O +_) ⟩
  O =∎


{- Binomial coefficients -}

binom : (n k : ℕ) → ℕ
binom   O     O   = 1
binom   O   (S k) = O
binom (S n)   O   = 1
binom (S n) (S k) = binom n k + binom n (S k)

binom-n-O : (n : ℕ) → binom n O == 1
binom-n-O O = idp
binom-n-O (S n) = idp

binom-n-1 : (n : ℕ) → binom n 1 == n
binom-n-1 O = idp
binom-n-1 (S n) = ap (_+ binom n 1) (binom-n-O n) ∙ ap S (binom-n-1 n)

abstract
  binom=O-rec : {k : ℕ} (n : ℕ) → binom n k == O → binom n (S k) == O
  binom=O-rec O _ = idp
  binom=O-rec {S k} (S n) p = ℕ-O+O binom-n-Sk (binom=O-rec n binom-n-Sk)
    where
    binom-n-Sk : binom n (S k) == O
    binom-n-Sk = ℕ-+=O' p

binom-n-Sn : (n : ℕ) → binom n (S n) == O
binom-n-Sn O = idp
binom-n-Sn (S n) = ℕ-O+O (binom-n-Sn n) (binom=O-rec n (binom-n-Sn n))

binom-n-n : (n : ℕ) → binom n n == 1
binom-n-n O = idp
binom-n-n (S n) =
  (binom n n) + (binom n (S n)) =⟨ binom-n-Sn n |in-ctx ((binom n n) +_) ⟩
  (binom n n) + O =⟨ +-comm _ O ∙ binom-n-n n ⟩
  1 =∎

binom-Sn-n : (n : ℕ) → binom (S n) n == S n
binom-Sn-n O = idp
binom-Sn-n (S n) =
  binom (S n) n + (binom n n + binom n (S n))
    =⟨ ap (_+ (binom n n + binom n (S n))) (binom-Sn-n n)
     ∙ ap (λ ◻ → S n + (◻ + (binom n (S n)))) (binom-n-n n)
     ∙ ap (λ ◻ → S n + (1 + ◻)) (binom-n-Sn n)
     ⟩
  S n + (1 + O) =⟨ +-comm (S n) (1 + O) ⟩
  S (S n) =∎

n<binom-Sn-n : (n : ℕ) → n < binom (S n) n
n<binom-Sn-n n = tr (n <_) (! (binom-Sn-n n)) ltS

binom>O : ∀ m n → n ≤ m → O < binom m n
binom>O O O x = ltS
binom>O O (S n) (inl ())
binom>O (S m) O x = ltS
binom>O (S m) (S n) x = O<+ {binom m n} {binom m (S n)} (binom>O m n (≤-cancel-S x))


{-
{- ℕ equality -}

ℕ= : ℕ → ℕ → Bool
ℕ= O O = true
ℕ= O (S n) = false
ℕ= (S n) O = false
ℕ= (S m) (S n) = ℕ= m n
-}
