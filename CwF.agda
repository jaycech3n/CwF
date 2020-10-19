{-# OPTIONS --without-K #-}

module CwF where

open import Category

{- Strict categories with families as a generalized algebraic theory. -}

record StrictCwF {i} : Type (lsuc i) where
  {- Contexts and substitutions -}
  field
    C : StrictCategory {i}
  open StrictCategory C renaming
    ( Ob         to Con
    ; Hom        to Sub
    ; Ob-is-set  to Con-is-set
    ; Hom-is-set to Sub-is-set
    ) public
  -- + terminal object
  
  {- Types and terms

  In more classical/informal settings this part can be succinctly given as a
  Fam-valued presheaf. Here we want to have more control over our later
  definitions and also avoid formalizing all the requisite intermediate notions,
  so we'll just formulate everything explicitly from the get-go.
  -}
  field
    Ty    : Con → Type i
    _[_]  : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
    
    []-id : ∀ {Γ} {σ : Ty Γ}
          → (σ [ id ]) == σ
          
    []-⊙  : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε} {σ}
          → (σ [ g ⊙ f ]) == (σ [ g ] [ f ])
    
  field
    Tm    : ∀ {Γ} (σ : Ty Γ) → Type i
    _[_]ₜ  : ∀ {Γ Δ} {σ : Ty Δ} → Tm σ → (f : Sub Γ Δ) → Tm (σ [ f ])

    []ₜ-id : ∀ {Γ} {σ : Ty Γ} {t : Tm σ}
           → (t [ id ]ₜ) == t [ Tm ↓ []-id ]

    []ₜ-⊙ : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε} {σ} {t : Tm σ}
          → (t [ g ⊙ f ]ₜ) == (t [ g ]ₜ [ f ]ₜ) [ Tm ↓ []-⊙ ]

