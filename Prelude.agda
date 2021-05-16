{-# OPTIONS --without-K #-}

module Prelude where

open import HoTT
  renaming
  ( lsucc       to lsuc
  ; transport   to tr
  ; transp-∙    to tr-∙
  ; to-transp   to to-tr
  ; from-transp to from-tr
  ; [_] to ∥_∥ )
  public

private
  variable
    i j k : ULevel
    A : Type i


{- Notation -}

ex-falso = ⊥-elim


{- Coercions: instance search for automatic transport insertion -}

record Coerce {i j} (A : Type i) (B : Type j) : Type (lmax i j) where
  field coerce : A → B

open Coerce ⦃ ... ⦄ public

_↑ : ∀ {i j} {A B} → ⦃ Coerce {i} {j} A B ⦄ → A → B
t ↑  = coerce t


{- Rewriting transport -}

module _ {B : A → Type j} {x y : A} where

  tr-!-tr : {b : B x} (p : x == y)
            → tr B (! p) (tr B p b) == b
  tr-!-tr idp = idp

  tr-tr-! : {b : B y} (p : x == y)
            → tr B p (tr B (! p) b) == b
  tr-tr-! idp = idp

  tr!=-=tr : ∀ {b} {b'} {p : x == y}
             → b == tr B p b'
             → tr B (! p) b == b'
  tr!=-=tr {p = idp} idp = idp

  tr=-=tr! : ∀ {b} {b'} {p : x == y}
             → b == tr B (! p) b'
             → tr B p b == b'
  tr=-=tr! {p = idp} idp = idp

  =tr!-tr= : ∀ {b} {b'} {p : x == y}
             → tr B p b == b'
             → b == tr B (! p) b'
  =tr!-tr= {p = idp} idp = idp

  =tr-tr!= : ∀ {b} {b'} {p : x == y}
             → tr B (! p) b == b'
             → b == tr B p b'
  =tr-tr!= {p = idp} idp = idp

tr-ap-∙ : {B : Type j} {f : A → B} {C : B → Type k} {x y z : A}
          (p : x == y) (q : y == z) (c : C (f x))
          → tr C (ap f (p ∙ q)) c == tr C (ap f q) (tr C (ap f p) c)
tr-ap-∙ idp idp c = idp


{-
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

{- Old formulation using vectors -}

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
