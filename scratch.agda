{-# OPTIONS --without-K --termination-depth=4 #-}

open import SuitableSemicategories

module scratch ⦃ I : SuitableSemicategory ⦄ where
open SuitableSemicategory I
open import Shapes-scratch


SCT : ℕ → Type₁
-- SCT n is the type of sequences of type families (Aᵢ : Mᵢ → Type₀ | i < n).

M : (i : ℕ) → SCT i → Type₀
-- The matching object at level i. Depends on the data of all levels < i.

SCT O = Lift ⊤
SCT (1+ n) = Σ[ C ∈ SCT n ] (M n C → Type₀)

M[_,_,_] : (i h t : ℕ) (iS : is-shape i h t) → SCT i → Type₀

M O _ = ⊤
M (1+ i) = M[ 1+ i , i , Hom-size (1+ i) i ] (full-shape (1+ i) i ltS)


init : {n : ℕ} (i : ℕ) → i < n → SCT n → SCT i
init i ltS C = fst C
init i (ltSR u) C = init i u (fst C)
-- Takes the i-initial segment of C : SCT n.

init= : ∀ {n} i i' u u' C → (p : i == i')
        → init {n} i u C == init {n} i' u' C [ SCT ↓ p ]
init= i .i u u' C idp = prop-path <-is-prop u u' |in-ctx (λ x → init i x C)

A : {n : ℕ} (C : SCT n) (i : ℕ) (u : i < n)
    → M i (init i u C) → Type₀
-- A C i, for i < n, is the datum Aᵢ given by the n-truncated sequence C : SCT n.

A C i ltS = snd C
A C i (ltSR u) = A (fst C) i u

X : {n : ℕ} (C : SCT n) (i : ℕ) → i < n → Type₀
-- X presents the type-valued diagram derived from the sequence of Aᵢ's;
-- X C i is the total space Xᵢ.

X C i u = Σ (M i (init i u C)) (A C i u)

_↓_ : (h t : ℕ) → ℕ
h ↓ (1+ t) = h
O ↓ O = O
(1+ h) ↓ O = h

↓< : {i h t : ℕ} → is-shape i h t → (h ↓ t) < i
↓< {i} {O} {O} iS = hcond iS
↓< {i} {O} {1+ t} iS = hcond iS
↓< {i} {1+ h} {t} iS = ≤→<→< (↓≤ (1+ h) t) (hcond iS)
  where
  ↓≤ : ∀ h t → (h ↓ t) ≤ h
  ↓≤ h (1+ t) = lteE
  ↓≤ O O = lteE
  ↓≤ (1+ h) O = lteS

{-# TERMINATING #-}
-- This is an attempt to formulate `args` to give only the property used in the end:
args : (i h t : ℕ) (iS : is-shape i h t) (C : SCT i)
       → M[ i , h , t ] iS C → M (h ↓ t) (init (h ↓ t) (↓< iS) C)
-- Maybe adding an explicit witness that h < i will fix the termination errors?

M[ i , O , 1+ t ] iS C = Σ[ m ∈ M[ i , O , t ] iS' C ] A C O (hcond iS) unit
  where
  iS' = shape-from-next-t iS
M[ i , 1+ h , O ] iS = M[ i , h , Hom-size i h ] (shape-from-next-h iS)
M[ i , O , O ] iS _ = ⊤
M[ i , 1+ h , 2+ t ] iS C =
  Σ[ m ∈ M[ i , 1+ h , 1+ t ] iS' C ]
   ( A C (1+ h) (hcond iS') (args i (1+ h) (1+ t) iS' C m) )
  where
  iS' = shape-from-next-t iS
M[ i , 1+ h , 1+ O ] iS C =
  Σ[ m ∈ M[ i , 1+ h , O ] iS' C ]
   ( A C h u (args i (1+ h) O iS' C m) )
  where
  iS' = shape-from-next-t iS
  u = <-trans ltS (hcond iS')

M= : ∀ i i' C C' → (p : i == i') → C == C' [ SCT ↓ p ] → M i C == M i' C'
M= O .O C C' idp q = idp
M= (1+ i) .(1+ i) C C' idp q = q |in-ctx _

-- Simplification 1: no empty hom-sets.
module simp1 where
  postulate
    Hom-inhab : (i h : ℕ) → h < i → O < Hom-size i h

  ↓-lem : ∀ {i h} → h < i → (h ↓ Hom-size i h) == h
  ↓-lem {i} {h} u with Hom-size i h | inspect (Hom-size i) h
  ... | O | with-eq p = ⊥-rec (≮O O (tr (O <_) p (Hom-inhab i h u)))
  ... | 1+ t | _ = idp

open simp1

args i O O iS _ m = m
args i (1+ h) O iS C m = tr (idf _) p (args i h (Hom-size i h) iS' C m)
  where
  iS' = shape-from-next-h iS

  p : M (h ↓ Hom-size i h) (init (h ↓ Hom-size i h) (↓< iS') C)
      == M h (init h (<-trans ltS (hcond iS)) C)
  p = M= (h ↓ Hom-size i h) h
        (init (h ↓ Hom-size i h) (↓< iS') C)
        (init h (<-trans ltS (hcond iS)) C)
        (↓-lem (hcond iS'))
        (init= (h ↓ Hom-size i h) h (↓< iS') (<-trans ltS (hcond iS)) C (↓-lem (hcond iS')))
args i O (1+ t) iS C m = unit
args i (1+ O) (1+ O) iS C m = {!!}
args i (1+ O) (2+ t) iS C m = {!!}
args i (2+ h) (1+ t) iS C m = {!!}
