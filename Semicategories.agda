{-# OPTIONS --without-K #-}

module Semicategories where

open import Prelude public


-- "Wild" constructions are those which are neither truncated nor required to be
-- coherent.

record WildSemicategoryOn {ℓ} (Ob : Type ℓ) : Type (lsuc ℓ) where
  infixr 40 _◦_
  field
    Hom : Ob → Ob → Type ℓ
    _◦_ : ∀ {x y z} → Hom y z → Hom x y → Hom x z
    ass : ∀ {x y z w} {f : Hom z w} {g : Hom y z} {h : Hom x y}
          → (f ◦ g) ◦ h == f ◦ (g ◦ h)

record WildSemicategory {ℓ} : Type (lsuc ℓ) where
  field
    Ob  : Type ℓ
    WildSemicategory-on-Ob : WildSemicategoryOn Ob
  open WildSemicategoryOn WildSemicategory-on-Ob public

record PreSemicategory {ℓ} : Type (lsuc ℓ) where
  field ⦃ C ⦄ : WildSemicategory {ℓ}
  open WildSemicategory C public
  field
    Hom-is-set : ∀ {x y} → is-set (Hom x y)

record StrictSemicategory {ℓ} : Type (lsuc ℓ) where
  field ⦃ C ⦄ : PreSemicategory {ℓ}
  open PreSemicategory C hiding (C) public
  field
    Ob-is-set  : is-set Ob


{- Properties of objects -}

module _ {ℓ} ⦃ C : WildSemicategory {ℓ} ⦄  where
  open WildSemicategory C

  is-initial : (x : Ob) → Type ℓ
  is-initial x = (y : Ob) → is-contr (Hom x y)

  is-terminal : (x : Ob) → Type ℓ
  is-terminal x = (y : Ob) → is-contr (Hom y x)
