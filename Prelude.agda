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

  dec-<S : m < S n → m ≤ n
  dec-<S ltS = inl idp
  dec-<S (ltSR x) = inr x

  dec-S< : S m < S n → m < S n
  dec-S< Sm<Sn = <-trans ltS Sm<Sn

  dec-S≤ : S m ≤ n → m < n
  dec-S≤ (inl x) = tr (_ <_) x ltS
  dec-S≤ (inr x) = <-trans ltS x

-- Automatically solve inequality conditions
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
  solve-S<S : {m n : ℕ} {h : m < n} → S m < S n
  solve-S<S {h = m<n} = <-ap-S m<n

instance
  solve-S≤S : {m n : ℕ} {h : m ≤ n} → S m ≤ S n
  solve-S≤S {h = m≤n} = ≤-ap-S m≤n

{- Natural numbers -}

ℕ-+=O  : {m n : ℕ} → m + n == O → m == O
ℕ-+=O {m = O} _ = idp

ℕ-+=O' : {m n : ℕ} → m + n == O → n == O
ℕ-+=O' {m = O} p = p
ℕ-+=O' {m = S m} {n} p = ex-falso (ℕ-S≠O (m + n) p)

ℕ-O+O : {m n : ℕ} → m == O → n == O → m + n == O
ℕ-O+O {m} {n} p q =
  m + n =⟨ p |in-ctx (_+ n) ⟩
  O + n =⟨ q |in-ctx (O +_) ⟩
  O =∎

-- Subtraction
diff : (m n : ℕ) ⦃ lt : m < n ⦄ → ℕ
diff O n = n
diff (S m) (S n) ⦃ lt ⦄ = diff m n ⦃ <-cancel-S lt ⦄

-- Equality
ℕ= : ℕ → ℕ → Bool
ℕ= O O = true
ℕ= O (S n) = false
ℕ= (S n) O = false
ℕ= (S m) (S n) = ℕ= m n

{- Combinations -}

instance
  Fin-coercion : ∀ {n} → Coerceable (Fin n) ℕ
  coerce ⦃ Fin-coercion ⦄ = fst

infix 50 _ch_
_ch_ : (n k : ℕ) → ℕ
O ch O = 1
O ch (S k) = O
(S n) ch O = 1
(S n) ch (S k) = (n ch k) + (n ch S k)

n-ch-O : (n : ℕ) → n ch O == 1
n-ch-O O = idp
n-ch-O (S n) = idp

n-ch-1 : (n : ℕ) → n ch 1 == n
n-ch-1 O = idp
n-ch-1 (S n) = ap (_+ (n ch 1)) (n-ch-O n) ∙ ap S (n-ch-1 n)

instance
  Fin-ch-1-coercion : ∀ {n} → Coerceable (Fin (n ch 1)) (Fin n)
  coerce ⦃ Fin-ch-1-coercion {n} ⦄ = tr Fin (n-ch-1 n)

abstract
  ch=O-rec : {k : ℕ} (n : ℕ) → n ch k == O → n ch S k == O
  ch=O-rec O _ = idp
  ch=O-rec {S k} (S n) p = ℕ-O+O n-ch-Sk (ch=O-rec n n-ch-Sk)
    where
    n-ch-Sk : n ch S k == O
    n-ch-Sk = ℕ-+=O' p

n-ch-Sn : (n : ℕ) → n ch S n == O
n-ch-Sn O = idp
n-ch-Sn (S n) = ℕ-O+O (n-ch-Sn n) (ch=O-rec n (n-ch-Sn n))

n-ch-n : (n : ℕ) → n ch n == 1
n-ch-n O = idp
n-ch-n (S n) =
  (n ch n) + (n ch S n) =⟨ n-ch-Sn n |in-ctx ((n ch n) +_) ⟩
  (n ch n) + O =⟨ +-comm _ O ∙ n-ch-n n ⟩
  1 =∎

Sn-ch-n : (n : ℕ) → S n ch n == S n
Sn-ch-n O = idp
Sn-ch-n (S n) =
  (S n ch n) + ((n ch n) + (n ch S n))
    =⟨ ap (_+ ((n ch n) + (n ch S n))) (Sn-ch-n n)
     ∙ ap (λ ◻ → S n + (◻ + (n ch S n))) (n-ch-n n)
     ∙ ap (λ ◻ → S n + (1 + ◻)) (n-ch-Sn n)
     ⟩
  S n + (1 + O) =⟨ +-comm (S n) (1 + O) ⟩
  S (S n) =∎

n-<-Sn-ch-n : (n : ℕ) → n < (S n) ch n
n-<-Sn-ch-n n = tr (n <_) (! (Sn-ch-n n)) ltS

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
