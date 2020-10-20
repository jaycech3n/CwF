{-# OPTIONS --without-K #-}

module CwF where

open import Category renaming (⟨⟩ to <>; [_] to ∥_∥) public

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
  field
    ⟨⟩ : Con
    ⟨⟩-is-terminal : is-terminal ⟨⟩
  
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
          
    []-⊙  : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε} {σ : Ty Ε}
          → (σ [ g ⊙ f ]) == (σ [ g ] [ f ])

    Ty-is-set : ∀ {Γ} → is-set (Ty Γ)

  field
    Tm    : ∀ {Γ} → (σ : Ty Γ) → Type i
    _[_]ₜ : ∀ {Γ Δ} {σ : Ty Δ} → Tm σ → (f : Sub Γ Δ) → Tm (σ [ f ])

    []ₜ-id : ∀ {Γ} {σ : Ty Γ} {t : Tm σ}
           → (t [ id ]ₜ) == t [ Tm ↓ []-id ]

    []ₜ-⊙ : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε} {σ} {t : Tm σ}
          → (t [ g ⊙ f ]ₜ) == (t [ g ]ₜ [ f ]ₜ) [ Tm ↓ []-⊙ ]
          
    Tm-is-set : ∀ {Γ} {σ : Ty Γ} → is-set (Tm σ)

  {- Comprehensions: context extension and projection -}
  field
    _∷_ : (Γ : Con) (σ : Ty Γ) → Con
    p   : ∀ {Γ} → (σ : Ty Γ) → Sub (Γ ∷ σ) Γ
    ν   : ∀ {Γ} → (σ : Ty Γ) → Tm (σ [ p σ ])

  field
    ⟨_∣_⟩ : ∀ {Γ Δ} {σ : Ty Γ}
          → (f : Sub Δ Γ) (t : Tm (σ [ f ])) → Sub Δ (Γ ∷ σ)

    {-
    The universal property of comprehensions is given by the following η- and
    β-rules.
    -}
    ⟨∣⟩-id : ∀ {Γ} {σ : Ty Γ} → ⟨ p σ ∣ ν σ ⟩ == id

    ⟨∣⟩-⊙  : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε} {σ : Ty Ε} {t : Tm {Δ} (σ [ g ])}
           → ⟨ g ⊙ f ∣ tr! Tm []-⊙ (t [ f ]ₜ) ⟩ == ⟨ g ∣ t ⟩ ⊙ f
           -- Note the transport

    ⟨∣⟩-β1 : ∀ {Δ Γ} {f : Sub Δ Γ} {σ : Ty Γ} {t : Tm (σ [ f ])}
           → (p σ) ⊙ ⟨ f ∣ t ⟩ == f

    ⟨∣⟩-β2 : ∀ {Δ Γ} {f : Sub Δ Γ} {σ : Ty Γ} {t : Tm (σ [ f ])}
           → ((ν σ) [ ⟨ f ∣ t ⟩ ]ₜ) == t
             [ Tm ↓ ! ([]-⊙) ∙ ap (λ f → σ [ f ]) ⟨∣⟩-β1 ]
             -- There must be a nicer way to write this...
