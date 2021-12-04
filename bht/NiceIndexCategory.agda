{-# OPTIONS --without-K #-}

-- Just enough structure to do what we want

module bht.NiceIndexCategory where

open import lib.Equivalence public
open import Category public
open import Fin

-- "Finite" here means (untruncated) Bishop-finite, i.e. with explicit ordering
-- on the Homs.

record LocallyFiniteWildCategoryOn {i} (Ob : Type i) : Type (lsuc i) where
  field ⦃ C ⦄ : WildCategoryOn Ob
  open WildCategoryOn C public
  field
    Hom-fin : ∀ x y → Σ[ n ∈ ℕ ] (Hom x y ≃ Fin n)

  Hom-size : ∀ x y → ℕ
  Hom-size x y = fst (Hom-fin x y)

  Hom-ord : ∀ {x y} → Hom x y → Fin (Hom-size x y)
  Hom-ord {x} {y} f = –> (snd (Hom-fin x y)) f

  Hom-idx : ∀ {x y} → Fin (Hom-size x y) → Hom x y
  Hom-idx {x} {y} f = <– (snd (Hom-fin x y)) f

  _≈_ : ∀ {x y} → Hom x y → Hom x y → Type₀
  f ≈ g = (Hom-ord f) == (Hom-ord g)

  _≺_ : ∀ {x y} → Hom x y → Hom x y → Type₀
  f ≺ g = (Hom-ord f) <-Fin (Hom-ord g)

  _≼_ : ∀ {x y} → Hom x y → Hom x y → Type₀
  f ≼ g = (Hom-ord f) ≤-Fin (Hom-ord g)

  _≈?_ : ∀ {x y} → Decidable (_≈_ {x} {y})
  f ≈? g = (Hom-ord f) ≟-Fin (Hom-ord g)

  _≺?_ : ∀ {x y} → Decidable (_≺_ {x} {y})
  f ≺? g = (Hom-ord f) <?-Fin (Hom-ord g)

  _≼?_ : ∀ {x y} → Decidable (_≼_ {x} {y})
  f ≼? g = (Hom-ord f) ≤?-Fin (Hom-ord g)

  Σ-Hom? : ∀ {ℓ} {x y} (P : Hom x y → Type ℓ)
           → ((f : Hom x y) → Dec (P f))
           → Dec (Σ[ f ∈ Hom x y ] (P f))
  Σ-Hom? P ∀Hom-Dec-P = {!!}

record NiceIndexCategory {i} : Type (lsuc i) where
  field ⦃ C ⦄ : LocallyFiniteWildCategoryOn ℕ
  open LocallyFiniteWildCategoryOn C hiding (C) public
