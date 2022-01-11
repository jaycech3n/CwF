{-# OPTIONS --without-K #-}

-- Just enough structure to do what we want

module bht.NiceIndexCategory where

open import lib.Equivalence public
open import Category public
open import Equivalence
open import Fin

-- "Finite" here means (untruncated) Bishop-finite, i.e. with explicit ordering
-- on the Homs.

record LocallyFiniteWildCategoryOn {i} (Ob : Type i) : Type (lsuc i) where
  field ⦃ C ⦄ : WildCategoryOn Ob
  open WildCategoryOn C public
  field
    Hom-fin : ∀ x y → Σ[ n ∈ ℕ ] (Hom x y ≃ Fin n)

  abstract
    Hom-size : (x y : Ob) → ℕ
    Hom-size x y = fst (Hom-fin x y)

    Hom-equiv : (x y : Ob) → Hom x y ≃ Fin (Hom-size x y)
    Hom-equiv x y = snd (Hom-fin x y)

    Hom-ord : ∀ {x y} → Hom x y → Fin (Hom-size x y)
    Hom-ord {x} {y} f = –> (Hom-equiv x y) f

    Hom-idx : ∀ x y → Fin (Hom-size x y) → Hom x y
    Hom-idx x y i = <– (Hom-equiv x y) i

    Hom-idx-of-ord : ∀ {x y} (f : Hom x y)
                     → Hom-idx x y (Hom-ord f) == f
    Hom-idx-of-ord {x} {y} f = <–-inv-l (Hom-equiv x y) f

    Hom-ord-of-idx : ∀ {x y} (i : Fin (Hom-size x y))
                     → Hom-ord (Hom-idx x y i) == i
    Hom-ord-of-idx {x} {y} i = <–-inv-r (Hom-equiv x y) i

  Hom= : ∀ {x y} {f g : Hom x y}
         → Hom-ord f == Hom-ord g
         → f == g
  Hom= {x} {y} {f = f} {g = g} p =
    f =⟨ ! (Hom-idx-of-ord f) ⟩
    Hom-idx x y (Hom-ord f) =⟨ ap (Hom-idx x y) p ⟩
    Hom-idx x y (Hom-ord g) =⟨ Hom-idx-of-ord g ⟩
    g =∎

  _≟-Hom_ : ∀ {x y} → has-dec-eq (Hom x y)
  f ≟-Hom g with Hom-ord f ≟-Fin Hom-ord g
  ...          | inl  eq = inl (Hom= eq)
  ...          | inr ¬eq = inr (¬eq ∘ ap Hom-ord)

  abstract
    _≺_ : ∀ {x y} → Hom x y → Hom x y → Type₀
    f ≺ g = (Hom-ord f) <-Fin (Hom-ord g)

    _≺?_ : ∀ {x y} → Decidable (_≺_ {x} {y})
    f ≺? g = (Hom-ord f) <?-Fin (Hom-ord g)

    <-Fin→≺ : ∀ {x y} {f g : Hom x y}
              → Hom-ord f <-Fin Hom-ord g
              → f ≺ g
    <-Fin→≺ u = u

    ≺→<-Fin : ∀ {x y} {f g : Hom x y}
              → f ≺ g
              → Hom-ord f <-Fin Hom-ord g
    ≺→<-Fin u = u

  _≼_ : ∀ {x y} → Hom x y → Hom x y → Type i
  f ≼ g = (f == g) ⊔ (f ≺ g)

  _≼?_ : ∀ {x y} → Decidable (_≼_ {x} {y})
  f ≼? g with Hom-ord f ≤?-Fin Hom-ord g
  ... | inl (inl p) = inl (inl (Hom= (Fin= p)))
  ... | inl (inr u) = inl (inr (<-Fin→≺ u))
  ... | inr ¬eq = inr (λ{(inl p) → ¬eq (inl (ap (to-ℕ ∘ Hom-ord) p))
                       ; (inr u) → ¬eq (inr (≺→<-Fin u))})

  module ≺-Reasoning where
    ≺-trans : ∀ {x y} {f g h : Hom x y} → f ≺ g → g ≺ h → f ≺ h
    ≺-trans f≺g g≺h = <-Fin→≺ (<-trans (≺→<-Fin f≺g) (≺→<-Fin g≺h))

    ≼-trans : ∀ {x y} {f g h : Hom x y} → f ≼ g → g ≼ h → f ≼ h
    ≼-trans u (inl idp) = u
    ≼-trans (inl idp) = λ v → v
    ≼-trans (inr u) (inr v) = inr (≺-trans u v)

    ≤-Fin→≼ : ∀ {x y} {f g : Hom x y}
              → Hom-ord f ≤-Fin Hom-ord g
              → f ≼ g
    ≤-Fin→≼ (inl p) = inl (Hom= (Fin= p))
    ≤-Fin→≼ (inr u) = inr (<-Fin→≺ u)

    ≼→≤-Fin : ∀ {x y} {f g : Hom x y}
             → f ≼ g
             → Hom-ord f ≤-Fin Hom-ord g
    ≼→≤-Fin (inl f=g) = inl (ap (to-ℕ ∘ Hom-ord) f=g)
    ≼→≤-Fin (inr f≺g) = inr (≺→<-Fin f≺g)

    ≼idx0→idx0 : ∀ {x y} {size-cond : O < Hom-size x y} {f : Hom x y}
                 → f ≼ Hom-idx x y (O , size-cond)
                 → f == Hom-idx x y (O , size-cond)
    ≼idx0→idx0 (inl p) = p
    ≼idx0→idx0 {f = f} (inr u) =
      ⊥-elim (≮O _ (tr (λ □ → to-ℕ (Hom-ord f) < to-ℕ □)
                       (Hom-ord-of-idx (O , _)) (≺→<-Fin u)))


  Σ-Hom? : ∀ {ℓ} {x y} (P : Hom x y → Type ℓ)
           → ((f : Hom x y) → Dec (P f))
           → Dec (Σ[ f ∈ Hom x y ] (P f))
  Σ-Hom? {ℓ} {x} {y} P u =
    tr (Dec ∘ Σ (Hom x y)) (λ= (ap P ∘ <–-inv-l e)) dec-Hom
    where
      n = fst (Hom-fin x y)
      e : Hom x y ≃ Fin n
      e = snd (Hom-fin x y)

      u' : (i : Fin n) → Dec (P (<– e i))
      u' = tr-Π-≃-r (Dec ∘ P) e u

      dec-Fin : Dec (Σ[ i ∈ Fin n ] P (<– e i))
      dec-Fin = Σ-Fin? (P ∘ (<– e)) u'

      dec-Hom : Dec (Σ[ f ∈ Hom x y ] P (<– e (–> e f)))
      dec-Hom with dec-Fin
      ...        | inl  u = inl (tr-Σ-≃-l (P ∘ <– e) e u)
      ...        | inr ¬u = inr (λ (f , p) → ¬u (–> e f , p))

  Hom-id-size : ∀ {x} → O < Hom-size x x
  Hom-id-size {x} with Hom-size x x | Hom-ord (id {x})
  ... | O    | i = ⊥-elim (≮O _ (snd i))
  ... | 1+ n | _ = O<S n


record NiceIndexCategory {ℓ} : Type (lsuc ℓ) where
  field ⦃ C ⦄ : LocallyFiniteWildCategoryOn ℕ
  open LocallyFiniteWildCategoryOn C hiding (C) public
  field
    ◦-monotone : ∀ {x y z} {g g' : Hom x y} {f : Hom y z}
                   → g ≺ g'
                   → f ◦ g ≺ f ◦ g'

  ◦-monotone' : ∀ {x y z} {g g' : Hom x y} {f : Hom y z}
                  → g ≼ g'
                  → f ◦ g ≼ f ◦ g'
  ◦-monotone' {f = f} (inl g=g') = inl (ap (f ◦_) g=g')
  ◦-monotone' (inr g≺g') = inr (◦-monotone g≺g')

  -- Note: the construction in bht.SCT is that of the type-theoretic Reedy
  -- fibrant diagram over the full direct subcategory of a nice index category
  -- whose degree map is given by deg n = n.
