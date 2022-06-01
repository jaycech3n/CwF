{-# OPTIONS --without-K #-}

module SuitableSemicategory where

open import Semicategory public
open import Equivalence
open import Fin


record LocallyFiniteSemicategoryOn {ℓ} (Ob : Type ℓ) : Type (lsuc ℓ) where
  field ⦃ C ⦄ : WildSemicategoryOn Ob
  open WildSemicategoryOn C public
  field
    Hom-fin : ∀ x y → Σ[ n ∈ ℕ ] (Hom x y ≃ Fin n)

  Hom-size : (x y : Ob) → ℕ
  Hom-size x y = fst (Hom-fin x y)

  Hom-equiv : (x y : Ob) → Hom x y ≃ Fin (Hom-size x y)
  Hom-equiv x y = snd (Hom-fin x y)

  idx-of : ∀ {x y} → Hom x y → Fin (Hom-size x y)
  idx-of {x} {y} f = –> (Hom-equiv x y) f

  Hom[_,_]# : ∀ x y → Fin (Hom-size x y) → Hom x y
  Hom[ x , y ]# i = <– (Hom-equiv x y) i

  Hom#idx : ∀ {x y} (f : Hom x y)
            → Hom[ x , y ]# (idx-of f) == f
  Hom#idx {x} {y} f = <–-inv-l (Hom-equiv x y) f

  idx-of-Hom# : ∀ {x y} (i : Fin (Hom-size x y))
                → idx-of (Hom[ x , y ]# i) == i
  idx-of-Hom# {x} {y} i = <–-inv-r (Hom-equiv x y) i

  Hom-is-set : ∀ {x y} → is-set (Hom x y)
  Hom-is-set {x} {y} = is-set-≃-stable e' (Lift-level Fin-is-set)
                         where
                         n = Hom-size x y
                         e = Hom-equiv x y
                         e' : Lift {j = ℓ} (Fin n) ≃ Hom x y
                         e' = (lift-equiv ∘e e)⁻¹

  Hom= : ∀ {x y} {f g : Hom x y}
         → idx-of f == idx-of g
         → f == g
  Hom= {x} {y} {f = f} {g = g} p =
    f =⟨ ! (Hom#idx f) ⟩
    Hom[ x , y ]# (idx-of f) =⟨ ap Hom[ x , y ]# p ⟩
    Hom[ x , y ]# (idx-of g) =⟨ Hom#idx g ⟩
    g =∎

  _≟-Hom_ : ∀ {x y} → has-dec-eq (Hom x y)
  f ≟-Hom g with idx-of f ≟-Fin idx-of g
  ...          | inl  eq = inl (Hom= eq)
  ...          | inr ¬eq = inr (¬eq ∘ ap idx-of)

  Σ-Hom? : ∀ {ℓ} {x y} (P : Hom x y → Type ℓ)
           → ((f : Hom x y) → Dec (P f))
           → Dec (Σ[ f ∈ Hom x y ] (P f))
  Σ-Hom? {ℓ} {x} {y} P u =
    tr (Dec ∘ Σ (Hom x y)) (λ= (ap P ∘ <–-inv-l e)) dec-Hom
    where
      n = Hom-size x y
      e = Hom-equiv x y

      u' : (i : Fin n) → Dec (P (<– e i))
      u' = tr-Π-≃-r (Dec ∘ P) e u

      dec-Fin : Dec (Σ[ i ∈ Fin n ] P (<– e i))
      dec-Fin = Σ-Fin? (P ∘ (<– e)) u'

      dec-Hom : Dec (Σ[ f ∈ Hom x y ] P (<– e (–> e f)))
      dec-Hom with dec-Fin
      ...        | inl  u = inl (tr-Σ-≃-l (P ∘ <– e) e u)
      ...        | inr ¬u = inr (λ (f , p) → ¬u (–> e f , p))


record SuitableSemicategory : Type₁ where
  field ⦃ C ⦄ : LocallyFiniteSemicategoryOn ℕ
  open LocallyFiniteSemicategoryOn C hiding (C) public
  field
    Hom-inverse : ∀ m n → Hom n m → m < n

  {-
  abstract
    _≺_ : ∀ {x y} → Hom x y → Hom x y → Type₀
    f ≺ g = (idx-of f) <-Fin (idx-of g)

    _≺?_ : ∀ {x y} → Decidable (_≺_ {x} {y})
    f ≺? g = (idx-of f) <?-Fin (idx-of g)

    <-Fin→≺ : ∀ {x y} {f g : Hom x y}
              → idx-of f <-Fin idx-of g
              → f ≺ g
    <-Fin→≺ u = u

    ≺→<-Fin : ∀ {x y} {f g : Hom x y}
              → f ≺ g
              → idx-of f <-Fin idx-of g
    ≺→<-Fin u = u

  _≼_ : ∀ {x y} → Hom x y → Hom x y → Type ℓ
  f ≼ g = (f == g) ⊔ (f ≺ g)

  _≼?_ : ∀ {x y} → Decidable (_≼_ {x} {y})
  f ≼? g with idx-of f ≤?-Fin idx-of g
  ... | inl (inl p) = inl (inl (Hom= (Fin= p)))
  ... | inl (inr u) = inl (inr (<-Fin→≺ u))
  ... | inr ¬eq = inr (λ{(inl p) → ¬eq (inl (ap (to-ℕ ∘ idx-of) p))
                       ; (inr u) → ¬eq (inr (≺→<-Fin u))})

  abstract
    Hom-size-witness : ∀ {x y} → Hom x y → O < Hom-size x y
    Hom-size-witness {x} {y} f =
      ≠O→O< (λ p → –> Fin-equiv-Empty (tr Fin p (idx-of f)))

  module ≺-Reasoning {x y : Ob} where
    ≺-trans : {f g h : Hom x y} → f ≺ g → g ≺ h → f ≺ h
    ≺-trans f≺g g≺h = <-Fin→≺ (<-trans (≺→<-Fin f≺g) (≺→<-Fin g≺h))

    ≼-trans : {f g h : Hom x y} → f ≼ g → g ≼ h → f ≼ h
    ≼-trans u (inl idp) = u
    ≼-trans (inl idp) = λ v → v
    ≼-trans (inr u) (inr v) = inr (≺-trans u v)

    ≼→≺→≺ : {f g h : Hom x y} → f ≼ g → g ≺ h → f ≺ h
    ≼→≺→≺ (inl idp) v = v
    ≼→≺→≺ (inr u) v = ≺-trans u v

    ≼→≺→≼ : {f g h : Hom x y} → f ≼ g → g ≺ h → f ≼ h
    ≼→≺→≼ (inl idp) v = inr v
    ≼→≺→≼ (inr u) v = inr (≺-trans u v)

    ≤-Fin→≼ : {f g : Hom x y} → idx-of f ≤-Fin idx-of g → f ≼ g
    ≤-Fin→≼ (inl p) = inl (Hom= (Fin= p))
    ≤-Fin→≼ (inr u) = inr (<-Fin→≺ u)

    ≼→≤-Fin : {f g : Hom x y} → f ≼ g → idx-of f ≤-Fin idx-of g
    ≼→≤-Fin (inl f=g) = inl (ap (to-ℕ ∘ idx-of) f=g)
    ≼→≤-Fin (inr f≺g) = inr (≺→<-Fin f≺g)

    ¬≺ : {f : Hom x y} → ¬ (f ≺ f)
    ¬≺ {f} = ¬-< ∘ ≺→<-Fin

    module _ {size-cond : O < Hom-size x y} where
      O-Fin = O , size-cond

      ≼idx0→idx0 : ∀ {f} → f ≼ Hom[ x , y ]# O-Fin → f == Hom[ x , y ]# O-Fin
      ≼idx0→idx0 (inl p) = p
      ≼idx0→idx0 {f = f} (inr u) =
        ⊥-elim (≮O _ (tr (λ □ → to-ℕ (idx-of f) < to-ℕ □)
                         (idx-of-Hom# O-Fin) (≺→<-Fin u)))

      idx0≼ : ∀ f → Hom[ x , y ]# O-Fin ≼ f
      idx0≼ f = ≤-Fin→≼ (tr (_≤-Fin (idx-of f)) (! (idx-of-Hom# _)) (O≤ _))

      ≺→idx0≺ : ∀ {f g} → f ≺ g → Hom[ x , y ]# O-Fin ≺ g
      ≺→idx0≺ {f} u = ≼→≺→≺ (idx0≼ f) u
  -}
