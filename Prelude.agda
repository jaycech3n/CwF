{-# OPTIONS --without-K #-}

{--- Prelude ---

A not-too-well organized jumble of material we need to develop CwFs and
semisimplicial types. ---}

module Prelude where

open import HoTT
  renaming
  ( lsucc       to lsuc
  ; transport   to tr
  ; transp-∙    to tr-∙
  ; to-transp   to to-tr
  ; from-transp to from-tr )
  hiding
  ( _⊆_ )
  public

private
  variable
    i j k : ULevel
    A : Type i

{- Notation -}

ex-falso = ⊥-elim

{- Coercions

Instance search for automatic insertion of the right transports.
-}

record Coerceable {i j} (A : Type i) (B : Type j) : Type (lmax i j) where
  field
    coerce : A → B

open Coerceable ⦃ ... ⦄ public

_↗ : ∀ {i j} {A B} ⦃ coerceable : Coerceable {i} {j} A B ⦄ → A → B
t ↗  = coerce t

{- Rewriting transports -}

module _ {B : A → Type j} {x y : A} where
  tr-!-tr : {b : B x} (p : x == y) → tr B (! p) (tr B p b) == b
  tr-!-tr idp = idp

  tr-tr-! : {b : B y} (p : x == y) → tr B p (tr B (! p) b) == b
  tr-tr-! idp = idp

  tr!=-if-=tr : ∀ {b} {b'} {p : x == y} (p' : b == tr B p b')
              → tr B (! p) b == b'
  tr!=-if-=tr {p = idp} idp = idp

  tr=-if-=tr! : ∀ {b} {b'} {p : x == y} (p' : b == tr B (! p) b')
              → tr B p b == b'
  tr=-if-=tr! {p = idp} idp = idp

  =tr!-if-tr= : ∀ {b} {b'} {p : x == y} (p' : tr B p b == b')
              → b == tr B (! p) b'
  =tr!-if-tr= {p = idp} idp = idp

  =tr-if-tr!= : ∀ {b} {b'} {p : x == y} (p' : tr B (! p) b == b')
              → b == tr B p b'
  =tr-if-tr!= {p = idp} idp = idp

tr-ap-∙ : {B : Type j} {f : A → B} {C : B → Type k}
          {x y z : A} (p : x == y) (q : y == z) (c : C (f x))
        → tr C (ap f (p ∙ q)) c == tr C (ap f q) (tr C (ap f p) c)
tr-ap-∙ idp idp c = idp

{- (In)equalities -}

module _ {m n : ℕ} where
  =-cancel-S : _==_ {A = ℕ} (S m) (S n) → m == n
  =-cancel-S idp = idp

  decr-<S : m < S n → m ≤ n
  decr-<S ltS = inl idp
  decr-<S (ltSR x) = inr x

  decr-S< : S m < S n → m < S n
  decr-S< Sm<Sn = <-trans ltS Sm<Sn

  decr-S≤ : S m ≤ n → m < n
  decr-S≤ (inl x) = tr (_ <_) x ltS
  decr-S≤ (inr x) = <-trans ltS x

-- Automatically solve (in)equality conditions
instance
  solve-≤-refl : {n : ℕ} → n ≤ n
  solve-≤-refl = lteE

instance
  solve-O≤ : {n : ℕ} → O ≤ n
  solve-O≤ {n} = O≤ n

instance
  solve-O<S : {n : ℕ} → O < S n
  solve-O<S {n} = O<S n

instance
  solve-n<S : {n : ℕ} → n < S n
  solve-n<S = ltS

instance
  solve-S<S : {m n : ℕ} ⦃ h : m < n ⦄ → S m < S n
  solve-S<S ⦃ h = m<n ⦄ = <-ap-S m<n

instance
  solve-S≤S : {m n : ℕ} ⦃ h : m ≤ n ⦄ → S m ≤ S n
  solve-S≤S ⦃ h = m≤n ⦄ = ≤-ap-S m≤n

O<+ : ∀ {m n} → O < m → O < m + n
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

ℕ= : ℕ → ℕ → Bool
ℕ= O O = true
ℕ= O (S n) = false
ℕ= (S n) O = false
ℕ= (S m) (S n) = ℕ= m n

{- Combinations -}

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

n-<-binom-Sn-n : (n : ℕ) → n < binom (S n) n
n-<-binom-Sn-n n = tr (n <_) (! (binom-Sn-n n)) ltS

binom>O : ∀ m n → n ≤ m → O < binom m n
binom>O O O x = ltS
binom>O O (S n) (inl ())
binom>O (S m) O x = ltS
binom>O (S m) (S n) x = O<+ {binom m n} {binom m (S n)} (binom>O m n (≤-cancel-S x))

{- Bool -}

_and_ : Bool → Bool → Bool
true and x = x
false and x = false

_or_ : Bool → Bool → Bool
true or x = true
false or x = x

{- List -}

flatten : {A : Type i} → List (List A) → List A
flatten nil = nil
flatten (x :: xs) = x ++ flatten xs

-- Ranges over ℕ
range : (m n : ℕ) → List ℕ
range O O = O :: nil
range O (S n) = snoc (range O n) (S n)
range (S m) O = nil
range (S m) (S n) = map S (range m n)

{- ℕ-sequences -}

infixr 60 _::_
infix 61 _::∎

-- Seq is isomorphic to (List ℕ \ nil)
data Seq : Type₀ where
  _::∎ : ℕ → Seq
  _::_ : ℕ → Seq → Seq

-- Increasing sequences of length l in {m,...,n} in lexicographic order
Seq+ : (l m n : ℕ) ⦃ nz : O < l ⦄ → List Seq
Seq+ (S O) m n = map _::∎ (range m n)
Seq+ (S (S l)) m n = flatten (map (λ k → map (k ::_) (Seq+ (S l) (S k) n))
                                  (range m n))

-- Subsequences
_⊆_ : Seq → Seq → Bool
(x ::∎) ⊆ (y ::∎) = ℕ= x y
(x ::∎) ⊆ (y :: ys) = ℕ= x y or (x ::∎ ⊆ ys)
(x :: xs) ⊆ (y ::∎) = false
(x :: xs) ⊆ (y :: ys) = (ℕ= x y and (xs ⊆ ys)) or (x :: xs ⊆ ys)

_⊂_ : Seq → Seq → Bool
(x ::∎) ⊂ (y ::∎) = false
(x ::∎) ⊂ (y :: ys) = ℕ= x y or (x ::∎ ⊂ ys)
(x :: xs) ⊂ (y ::∎) = false
(x :: xs) ⊂ (y :: ys) = (ℕ= x y and (xs ⊂ ys)) or (x :: xs ⊆ ys)

{- Old formulation using vectors

infixr 60 _::_
data Vec (A : Type i) : ℕ → Type (lsuc i) where
  ⟦⟧   : Vec A O
  _::_ : {n : ℕ} → A → Vec A n → Vec A (S n)

module _ {A : Type i} {B : Type i} where
  vmap : ∀ {n} (f : A → B) → Vec A n → Vec B n
  vmap _ ⟦⟧ = ⟦⟧
  vmap f (a :: as) = f a :: vmap f as

Seq' : ℕ → Type₁
Seq' = Vec ℕ

Seq'+ : (l m n : ℕ) → List (Seq' l)
Seq'+ O _ _ = ⟦⟧ :: nil
Seq'+ (S l) m n = flatten (map (λ k → map (k ::_) (Seq'+ l (S k) n)) (range m n))
-}
