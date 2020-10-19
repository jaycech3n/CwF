{-# OPTIONS --without-K #-}

{- Various notions of categories in HoTT -}

module Category where

open import HoTT renaming (lsucc to lsuc; [_] to ∥_∥) public

record WildCategory {i} : Type (lsuc i) where
  infix 40 _⊙_
  field
    Ob  : Type i
    Hom : Ob → Ob → Type i
    _⊙_ : ∀ {x y z} → Hom y z → Hom x y → Hom x z
    id  : ∀ {x} → Hom x x

    ass : ∀ {x y z w} {f : Hom x y} {g : Hom y z} {h : Hom z w}
        → (h ⊙ g) ⊙ f == h ⊙ (g ⊙ f)
    idl : ∀ {x y} {f : Hom x y} → id ⊙ f == f
    idr : ∀ {x y} {f : Hom x y} → f ⊙ id == f

record PreCategory {i} : Type (lsuc i) where
  field {{C}} : WildCategory {i}
  open WildCategory C public
  field
    Hom-is-set : ∀ {x y} → is-set (Hom x y)

record StrictCategory {i} : Type (lsuc i) where
  field {{C}} : PreCategory {i}
  open PreCategory C public
  field
    Ob-is-set  : is-set Ob

-- Isomorphism is usually defined for precategories; we define it for wild ones.
module _ {i} {{C : WildCategory {i}}} where
  open WildCategory C
  
  record is-iso  {x y : Ob} (f : Hom x y) : Type i where
    field
      g : Hom y x
      g-f : g ⊙ f == id
      f-g : f ⊙ g == id

  infix 20 _≅_
  record _≅_ (x y : Ob) : Type i where
    field
      f : Hom x y
      f-is-iso : is-iso f

  -- Equal objects are isomorphic.
  id-to-iso : ∀ {x y} → x == y → x ≅ y
  id-to-iso {x} {.x} idp = record
    { f = id
    ; f-is-iso = record { g = id ; g-f = idl ; f-g = idl }
    }

record Category {i} : Type (lsuc i) where
  field {{C}} : PreCategory {i}
  open PreCategory C public
  field
    id-to-iso-is-equiv : (x y : Ob) → is-equiv (id-to-iso {i} {x} {y})

