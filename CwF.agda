{-# OPTIONS --without-K #-}

module CwF where

open import Category renaming
  ( ⟨⟩ to <>
  ; [_] to ∥_∥
  ; wild-of-strict to s→w-cat
  ) public

{- Categories with families

Formulated as generalized algebraic theories following Dybjer ("Internal Type Theory",
1996) and others.
-}
record WildCwFStructure {i} (C : WildCategory {i}) : Type (lsuc i) where
  open WildCategory C renaming
    ( Ob  to Con
    ; Hom to Sub
    ) public

  {- Empty context -}
  field
    ⟨⟩ : Con
    ⟨⟩-is-terminal : is-terminal {{C}} ⟨⟩
  
  {- Types and terms -}
  field
    Ty    : Con → Type i
    _[_]  : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
    
    []-id : ∀ {Γ} {σ : Ty Γ}
          → (σ [ id ]) == σ
          
    []-⊙ : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε} {σ : Ty Ε}
         → (σ [ g ⊙ f ]) == (σ [ g ] [ f ])

  field
    Tm   : ∀ {Γ} (σ : Ty Γ) → Type i
    _[_]ₜ : ∀ {Γ Δ} {σ : Ty Δ} → Tm σ → (f : Sub Γ Δ) → Tm (σ [ f ])

    []ₜ-id : ∀ {Γ} {σ : Ty Γ} {t : Tm σ}
           → (t [ id ]ₜ) == t [ Tm ↓ []-id ]

    []ₜ-⊙ : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε} {σ} {t : Tm σ}
          → (t [ g ⊙ f ]ₜ) == (t [ g ]ₜ [ f ]ₜ) [ Tm ↓ []-⊙ ]

  {- Comprehensions: context extension and projections -}
  field
    _∷_ : (Γ : Con) (σ : Ty Γ) → Con
    p   : ∀ {Γ} (σ : Ty Γ) → Sub (Γ ∷ σ) Γ
    ν   : ∀ {Γ} (σ : Ty Γ) → Tm (σ [ p σ ])

  field
    ⟨_∣_⟩ : ∀ {Γ Δ} {σ : Ty Γ} (f : Sub Δ Γ) (t : Tm (σ [ f ])) → Sub Δ (Γ ∷ σ)

    {-
    The universal property of comprehensions is given by the following β- and
    η-rules.
    -}
    ⟨∣⟩-β1 : ∀ {Δ Γ} {f : Sub Δ Γ} {σ : Ty Γ} {t : Tm (σ [ f ])}
           → (p σ) ⊙ ⟨ f ∣ t ⟩ == f

    ⟨∣⟩-β2 : ∀ {Δ Γ} {f : Sub Δ Γ} {σ : Ty Γ} {t : Tm (σ [ f ])}
           → (ν σ [ ⟨ f ∣ t ⟩ ]ₜ) == t
             [ Tm ↓ ! ([]-⊙) ∙ ap (λ f → σ [ f ]) ⟨∣⟩-β1 ]
             
    ⟨∣⟩-id : ∀ {Γ} {σ : Ty Γ} → ⟨ p σ ∣ ν σ ⟩ == id

    ⟨∣⟩-⊙ : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε} {σ : Ty Ε} {t : Tm {Δ} (σ [ g ])}
           → ⟨ g ⊙ f ∣ tr! Tm []-⊙ (t [ f ]ₜ) ⟩ == ⟨ g ∣ t ⟩ ⊙ f

record StrictCwFStructure {i} (C : StrictCategory {i}) : Type (lsuc i) where
  field
    {{W}} : WildCwFStructure (s→w-cat C)
    
  open StrictCategory C renaming
    ( Ob-is-set  to Con-is-set
    ; Hom-is-set to Sub-is-set
    ) public
  open WildCwFStructure W public

  {- Additional truncation requirements -}
  field
    Ty-is-set : ∀ {Γ} → is-set (Ty Γ)
    Tm-is-set : ∀ {Γ} {σ : Ty Γ} → is-set (Tm σ)

-- Coercion
wild-of-strict : ∀ {i} {C : StrictCategory {i}}
        → StrictCwFStructure C → WildCwFStructure (s→w-cat C)
wild-of-strict = StrictCwFStructure.W

{- Additional structure

To avoid names getting too long we introduce the prefixes [w], [W] for "wild"
notions, and [s], [S] for "strict" ones.
-}

record PiStructure {i}
  {C : StrictCategory {i}} (sCwF : StrictCwFStructure C) : Type (lsuc i)
  where
  open StrictCwFStructure sCwF public
  
  field
    ̂Π   : ∀ {Γ} (A : Ty Γ) (B : Ty (Γ ∷ A)) → Ty Γ
    ̂λ   : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ∷ A)} (b : Tm B) → Tm (̂Π A B)
    -- _`_ :
    -- TBC
