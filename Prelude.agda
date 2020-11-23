{-# OPTIONS --without-K #-}

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

{- Automatic coercions -}

record Coerceable {i j} (A : Type i) (B : Type j) : Type (lmax i j) where
  field
    coerce : A → B

open Coerceable {{...}} public

_↗ : ∀ {i j} {A B} {{coerceable : Coerceable {i} {j} A B}} → A → B
t ↗  = coerce t

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
  0     =∎

{- Combinatorics -}

instance
  Fin-coercion : ∀ {n} → Coerceable (Fin n) ℕ
  coerce {{Fin-coercion}} = fst

infix 50 _ch_
_ch_ : (n k : ℕ) → ℕ
O ch O = 1
O ch (S k) = O
(S n) ch O = 1
(S n) ch (S k) = (n ch S k) + (n ch k)

abstract
  ch=O-rec : {k : ℕ} (n : ℕ) → n ch k == O → n ch S k == O
  ch=O-rec O _ = idp
  ch=O-rec {S k} (S n) p = ℕ-O+O (ch=O-rec n n-ch-Sk) n-ch-Sk
    where
    n-ch-Sk : n ch S k == O
    n-ch-Sk = ℕ-+=O p

n-ch-Sn : (n : ℕ) → n ch S n == O
n-ch-Sn O = idp
n-ch-Sn (S n) = ℕ-O+O (ch=O-rec n (n-ch-Sn n)) (n-ch-Sn n)

n-ch-n : (n : ℕ) → n ch n == 1
n-ch-n O = idp
n-ch-n (S n) =
  (n ch S n) + (n ch n) =⟨ n-ch-Sn n |in-ctx (_+ (n ch n)) ⟩
  0 + (n ch n) =⟨ n-ch-n n ⟩
  1 =∎

Sn-ch-n : (n : ℕ) → S n ch n == S n
Sn-ch-n O = idp
Sn-ch-n (S n) = ap (λ ◻ → ◻ + (n ch n) + (S n ch n)) (n-ch-Sn n)
              ∙ ap (_+ (S n ch n)) (n-ch-n n)
              ∙ ap S (Sn-ch-n n)

n-<-Sn-ch-n : (n : ℕ) → n < (S n) ch n
n-<-Sn-ch-n n = tr (n <_) (! (Sn-ch-n n)) ltS
