{-# OPTIONS --without-K #-}

{--- Prelude ---

A not-too-well organized jumble of material we need to develop CwFs and
semisimplicial types. ---}

module Prelude where

open import HoTT
  renaming
  ( lsucc     to lsuc
  ; transport to tr
  ; transp-∙  to tr-∙
  ; to-transp to to-tr
  ; from-transp to from-tr )
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

open Coerceable {{...}} public

_↗ : ∀ {i j} {A B} {{coerceable : Coerceable {i} {j} A B}} → A → B
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

{- Lists and vectors -}

flatten : {A : Type i} → List (List A) → List A
flatten nil = nil
flatten (x :: xs) = x ++ flatten xs

infixr 60 _::_
data Vec (A : Type i) : ℕ → Type (lsuc i) where
  ⟦⟧   : Vec A O
  _::_ : {n : ℕ} → A → Vec A n → Vec A (S n)

module _ {A : Type i} {B : Type i} where
  vmap : ∀ {n} (f : A → B) → Vec A n → Vec B n
  vmap _ ⟦⟧ = ⟦⟧
  vmap f (a :: as) = f a :: vmap f as

{- Natural numbers -}

ℕ-+=O  : {m n : ℕ} → m + n == 0 → m == 0
ℕ-+=O {m = O} _ = idp

ℕ-+=O' : {m n : ℕ} → m + n == 0 → n == 0
ℕ-+=O' {m = O} p = p
ℕ-+=O' {m = S m} {n} p = ex-falso (ℕ-S≠O (m + n) p)

ℕ-O+O : {m n : ℕ} → m == 0 → n == 0 → m + n == 0
ℕ-O+O {m} {n} p q =
  m + n =⟨ p |in-ctx (_+ n) ⟩
  0 + n =⟨ q |in-ctx (0 +_) ⟩
  0 =∎

{- Combinations -}

instance
  Fin-coercion : ∀ {n} → Coerceable (Fin n) ℕ
  coerce {{Fin-coercion}} = fst

infix 50 _ch_
_ch_ : (n k : ℕ) → ℕ
0 ch 0 = 1
0 ch (S k) = 0
(S n) ch 0 = 1
(S n) ch (S k) = (n ch k) + (n ch S k)

n-ch-0 : (n : ℕ) → n ch 0 == 1
n-ch-0 O = idp
n-ch-0 (S n) = idp

n-ch-1 : (n : ℕ) → n ch 1 == n
n-ch-1 O = idp
n-ch-1 (S n) = ap (_+ (n ch 1)) (n-ch-0 n) ∙ ap S (n-ch-1 n)

instance
  Fin-ch-1-coercion : ∀ {n} → Coerceable (Fin (n ch 1)) (Fin n)
  coerce {{Fin-ch-1-coercion {n}}} = tr Fin (n-ch-1 n)

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
  (n ch n) + 0 =⟨ +-comm _ 0 ∙ n-ch-n n ⟩
  1 =∎

Sn-ch-n : (n : ℕ) → S n ch n == S n
Sn-ch-n O = idp
Sn-ch-n (S n) =
  (S n ch n) + ((n ch n) + (n ch S n))
    =⟨ ap (_+ ((n ch n) + (n ch S n))) (Sn-ch-n n)
     ∙ ap (λ ◻ → S n + (◻ + (n ch S n))) (n-ch-n n)
     ∙ ap (λ ◻ → S n + (1 + ◻)) (n-ch-Sn n)
     ⟩
  S n + (1 + 0) =⟨ +-comm (S n) (1 + 0) ⟩
  S (S n) =∎

n-<-Sn-ch-n : (n : ℕ) → n < (S n) ch n
n-<-Sn-ch-n n = tr (n <_) (! (Sn-ch-n n)) ltS

{- Ranges over ℕ -}

range : (m n : ℕ) → List ℕ
range O O = 0 :: nil
range O (S n) = snoc (range 0 n) (S n)
range (S m) O = nil
range (S m) (S n) = map S (range m n)

{- Strictly increasing sequences of naturals -}

-- Slow!
ℕSeq+ : (l m n : ℕ) → List (Vec ℕ l)
ℕSeq+ 0 _ _ = ⟦⟧ :: nil
ℕSeq+ (S l) m n = flatten (map (λ k → map (k ::_) (ℕSeq+ l (S k) n)) (range m n))

-- Increasing sequences of length l in {0, ..., n - 1}
FinSeq+ : (l n : ℕ) → List (Vec ℕ l)
FinSeq+ l 0 = nil
FinSeq+ l (S n) = ℕSeq+ l 0 n

-- example = {!FinSeq+ 5 12!}
