{-# OPTIONS --without-K #-}

module Category where

open import Semicategory public


{- Categories -}

record WildCategoryOn {ℓ} (Ob : Type ℓ) : Type (lsuc ℓ) where
  field ⦃ WildSemicategory-on-Ob ⦄ : WildSemicategoryOn Ob
  open WildSemicategoryOn WildSemicategory-on-Ob public
  field
    id : ∀ {x} → Hom x x
    idl : ∀ {x y} {f : Hom x y} → id ◦ f == f
    idr : ∀ {x y} {f : Hom x y} → f ◦ id == f

record WildCategory {ℓ} : Type (lsuc ℓ) where
  field
    Ob  : Type ℓ
    WildCategory-on-Ob : WildCategoryOn Ob
  open WildCategoryOn WildCategory-on-Ob public

record PreCategory {ℓ} : Type (lsuc ℓ) where
  field ⦃ C ⦄ : WildCategory {ℓ}
  open WildCategory C public
  field
    Hom-is-set : ∀ {x y} → is-set (Hom x y)

record StrictCategory {ℓ} : Type (lsuc ℓ) where
  field ⦃ C ⦄ : PreCategory {ℓ}
  open PreCategory C hiding (C) public
  field
    Ob-is-set  : is-set Ob


{- Isomorphism -}

module _ {ℓ} ⦃ C : WildCategory {ℓ} ⦄ where
  open WildCategory C

  record is-iso  {x y : Ob} (f : Hom x y) : Type ℓ where
    field
      g : Hom y x
      g∘f : g ◦ f == id
      f∘g : f ◦ g == id

  infix 30 _≅_
  record _≅_ (x y : Ob) : Type ℓ where
    field
      f : Hom x y
      f-is-iso : is-iso f

  id-to-iso : ∀ {x y} → x == y → x ≅ y
  id-to-iso idp = record
    { f = id
    ; f-is-iso = record { g = id ; g∘f = idl ; f∘g = idl }
    }


{- Univalent category -}

record Category {ℓ} : Type (lsuc ℓ) where
  field ⦃ C ⦄ : PreCategory {ℓ}
  open PreCategory C hiding (C) public
  field
    id-to-iso-is-equiv : (x y : Ob) → is-equiv (id-to-iso {ℓ} {x} {y})


{- Coercions -}

wild-of-pre-cat = PreCategory.C
pre-of-strict-cat = StrictCategory.C
pre-of-cat = Category.C

wild-of-strict-cat : ∀ {ℓ} → StrictCategory {ℓ} → WildCategory {ℓ}
wild-of-strict-cat = wild-of-pre-cat ∘ pre-of-strict-cat

wild-of-cat : ∀ {ℓ} → Category {ℓ} → WildCategory {ℓ}
wild-of-cat = wild-of-pre-cat ∘ pre-of-cat

-- Semicategory structure

instance
  semi-of-wild-cat : ∀ {ℓ} ⦃ C : WildCategory {ℓ} ⦄ → WildSemicategory {ℓ}
  semi-of-wild-cat ⦃ C ⦄ = record
    { Ob = WildCategory.Ob C
    ; WildSemicategory-on-Ob =
        WildSemicategory-on-Ob (WildCategory.WildCategory-on-Ob C)
    }
    where open WildCategoryOn
