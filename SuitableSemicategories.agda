{-# OPTIONS --without-K #-}

module SuitableSemicategories where

open import Semicategories public


record LocallyFiniteSemicategoryOn {ℓ} (Ob : Type ℓ) : Type (lsuc ℓ) where
  field ⦃ C ⦄ : WildSemicategoryOn Ob
  open WildSemicategoryOn C public
  field
    Hom-fin : ∀ x y → Σ[ n ∈ ℕ ] (Hom x y ≃ Fin n)

  abstract
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

    idx-of<Hom-size : ∀ {x y} (f : Hom x y) → to-ℕ (idx-of f) < Hom-size x y
    idx-of<Hom-size f = snd (idx-of f)

  ℕ-idx-of : ∀ {x y} → Hom x y → ℕ
  ℕ-idx-of {x} {y} = to-ℕ ∘ idx-of {x} {y}

  Hom-is-set : ∀ {x y} → is-set (Hom x y)
  Hom-is-set {x} {y} = equiv-preserves-level e' ⦃ Lift-level Fin-is-set ⦄
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
  f ≟-Hom g = if (idx-of f ≟-Fin idx-of g)
                 (λ  p → inl (Hom= p))
                 (λ ¬p → inr (¬p ∘ ap idx-of))

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
      dec-Hom = if dec-Fin
                   (λ  u → inl (tr-Σ-≃-l (P ∘ <– e) e u))
                   (λ ¬u → inr (λ (f , p) → ¬u (–> e f , p)))

  -- The number of (g : Hom x y) satisfying f ≤ g and (P g)
  #-Hom[_,_]-from : ∀ {ℓ} x y
                    → (P : Hom x y → Type ℓ)
                    → ((f : Hom x y) → Dec (P f))
                    → (f : Hom x y)
                    → Σ[ k ∈ ℕ ] ℕ-idx-of f + k ≤ Hom-size x y
  #-Hom[ x , y ]-from P dec f =
    #-Fin-from {n = Hom-size x y} (P ∘ Hom[ x , y ]#) (dec ∘ Hom[ x , y ]#)
      (idx-of f) {Hom-size x y ∸ ℕ-idx-of f ∸ 1} {<→∸=S (snd (idx-of f))}

  _factors-through_ : ∀ {x y z} (h : Hom x z) (f : Hom x y) → Type ℓ
  _factors-through_ {y = y} {z} h f = Σ[ g ∈ Hom y z ] g ◦ f == h

  _factors-through?_ : ∀ {x y z} (h : Hom x z) (f : Hom x y)
                       → Dec (h factors-through f)
  h factors-through? f = Σ-Hom? (λ g → (g ◦ f) == h) (λ g → g ◦ f ≟-Hom h)

  Hom[_,_]-inhab : ∀ x y → Hom x y → O < Hom-size x y
  Hom[ x , y ]-inhab f = ≤→<→< (O≤ _) (snd (idx-of f))


record SuitableSemicategory : Type₁ where
  field ⦃ C ⦄ : LocallyFiniteSemicategoryOn ℕ
  open LocallyFiniteSemicategoryOn C hiding (C) public
  field
    Hom-inverse : ∀ n m → Hom n m → m < n

  abstract
    endo-Hom-empty : ∀ n → Hom-size n n == O
    endo-Hom-empty n with Hom-size n n | inspect (Hom-size n) n
    ... | O    | _ = idp
    ... | 1+ m | with-eq p =
      ⊥-elim (¬-< (Hom-inverse n n (Hom[ n , n ]# (m , tr (m <_) (! p) ltS))))


record WellOrientedSemicategory : Type₁ where
  field ⦃ C ⦄ : SuitableSemicategory
  open SuitableSemicategory C hiding (C) public
  field
    Hom-monotone : ∀ k m n (f : Hom n m) (g h : Hom m k)
                   → idx-of g <-Fin idx-of h
                   → idx-of (g ◦ f) ≤-Fin idx-of (h ◦ f)
