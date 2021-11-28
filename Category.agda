{--- Categories in HoTT ---}

{-# OPTIONS --without-K #-}

module Category where

open import Prelude public


{- Various flavors of "category" -}

-- "Wild" constructions are those which are neither truncated nor required to be
-- coherent.

record WildCategory {i} : Type (lsuc i) where
  infixr 40 _◦_
  field
    Ob  : Type i
    Hom : Ob → Ob → Type i
    _◦_ : ∀ {x y z} → Hom y z → Hom x y → Hom x z
    id  : ∀ {x} → Hom x x

    ass : ∀ {x y z w} {f : Hom z w} {g : Hom y z} {h : Hom x y}
          → (f ◦ g) ◦ h == f ◦ (g ◦ h)
    idl : ∀ {x y} {f : Hom x y} → id ◦ f == f
    idr : ∀ {x y} {f : Hom x y} → f ◦ id == f

record PreCategory {i} : Type (lsuc i) where
  field ⦃ C ⦄ : WildCategory {i}
  open WildCategory C public
  field
    Hom-is-set : ∀ {x y} → is-set (Hom x y)

record StrictCategory {i} : Type (lsuc i) where
  field ⦃ C ⦄ : PreCategory {i}
  open PreCategory C hiding (C) public
  field
    Ob-is-set  : is-set Ob

-- Isomorphism

module _ {i} ⦃ C : WildCategory {i} ⦄ where
  open WildCategory C

  record is-iso  {x y : Ob} (f : Hom x y) : Type i where
    field
      g : Hom y x
      g∘f : g ◦ f == id
      f∘g : f ◦ g == id

  infix 30 _≅_
  record _≅_ (x y : Ob) : Type i where
    field
      f : Hom x y
      f-is-iso : is-iso f

  id-to-iso : ∀ {x y} → x == y → x ≅ y
  id-to-iso idp = record
    { f = id
    ; f-is-iso = record { g = id ; g∘f = idl ; f∘g = idl }
    }

-- Univalent category

record Category {i} : Type (lsuc i) where
  field ⦃ C ⦄ : PreCategory {i}
  open PreCategory C hiding (C) public
  field
    id-to-iso-is-equiv : (x y : Ob) → is-equiv (id-to-iso {i} {x} {y})


{- Coercions -}

wild-of-pre-cat = PreCategory.C
pre-of-strict-cat = StrictCategory.C
pre-of-cat = Category.C

wild-of-strict-cat : ∀ {i} → StrictCategory {i} → WildCategory {i}
wild-of-strict-cat = wild-of-pre-cat ∘ pre-of-strict-cat

wild-of-cat : ∀ {i} → Category {i} → WildCategory {i}
wild-of-cat = wild-of-pre-cat ∘ pre-of-cat


{- Properties of objects -}

module _ {i} (C : WildCategory {i}) where
  open WildCategory C

  is-initial : (x : Ob) → Type i
  is-initial x = (y : Ob) → is-contr (Hom x y)

  is-terminal : (x : Ob) → Type i
  is-terminal x = (y : Ob) → is-contr (Hom y x)
