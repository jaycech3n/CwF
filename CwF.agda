{-# OPTIONS --without-K #-}

{- Categories with families

Formulated as generalized algebraic theories following Dybjer ("Internal Type
Theory", 1996) and others.
-}

module CwF where

open import Category renaming
  ( ⟨⟩ to <>
  ; [_] to ∥_∥
  ; wild-of-strict to s→w-cat
  ) public

{- Basic CwF structures -}
record WildCwFStructure {i} (C : WildCategory {i}) : Type (lsuc i) where
  open WildCategory C renaming
    ( Ob  to Con
    ; Hom to Sub
    ) public

  -- Empty context
  field
    ⟨⟩ : Con
    ⟨⟩-is-terminal : is-terminal {{C}} ⟨⟩
  
  -- Types and terms
  infix 40 _[_] _[_]ₜ
  field
    Ty    : Con → Type i
    _[_]  : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
    
    []-id : ∀ {Γ} {σ : Ty Γ}
            → (σ [ id ]) == σ
          
    []-⊙ : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε} {σ : Ty Ε}
           → (σ [ g ⊙ f ]) == (σ [ g ] [ f ])

    Tm   : ∀ {Γ} (σ : Ty Γ) → Type i
    _[_]ₜ : ∀ {Γ Δ} {σ : Ty Δ} → Tm σ → (f : Sub Γ Δ) → Tm (σ [ f ])

    []ₜ-id : ∀ {Γ} {σ : Ty Γ} {t : Tm σ}
             → (t [ id ]ₜ) == t [ Tm ↓ []-id ]

    []ₜ-⊙ : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε} {σ} {t : Tm σ}
            → (t [ g ⊙ f ]ₜ) == (t [ g ]ₜ [ f ]ₜ) [ Tm ↓ []-⊙ ]

  -- Comprehensions: context extension and projections
  infixl 30 _,,_
  field
    _∷_  : (Γ : Con) (σ : Ty Γ) → Con
    p    : ∀ {Γ} {σ : Ty Γ} → Sub (Γ ∷ σ) Γ
    ν    : ∀ {Γ} {σ : Ty Γ} → Tm (σ [ p ])
    _,,_ : ∀ {Γ Δ} {σ : Ty Γ} (f : Sub Δ Γ) (t : Tm (σ [ f ])) → Sub Δ (Γ ∷ σ)

    -- The universal property of comprehensions is given by the following β- and
    -- η-rules.
    ,,-β1 : ∀ {Δ Γ} {f : Sub Δ Γ} {σ : Ty Γ} {t : Tm (σ [ f ])}
            → p ⊙ (f ,, t) == f

    ,,-β2 : ∀ {Δ Γ} {f : Sub Δ Γ} {σ : Ty Γ} {t : Tm (σ [ f ])}
            → (ν [ f ,, t ]ₜ) == t [ Tm ↓ (! []-⊙) ∙ ap (λ f → σ [ f ]) ,,-β1 ]
             
    ,,-id : ∀ {Γ} {σ : Ty Γ} → (p {Γ} {σ} ,, ν {Γ} {σ}) == id

    ,,-⊙ : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε} {σ : Ty Ε} {t : Tm {Δ} (σ [ g ])}
           → (g ⊙ f ,, tr! Tm []-⊙ (t [ f ]ₜ)) == (g ,, t) ⊙ f

  -- Given `A : Ty Γ` and `f : Sub Δ Γ` we get the lifted substitution `f ↑ :
  -- Sub (Δ ∷ A [ f ]) (Γ ∷ A)` that acts on any type family `B : Ty (Γ ∷ A)` or
  -- dependent term `b : Tm (Γ ∷ A)` as `f` does, and leaves the "free variable
  -- x : A" alone.
  _↑ : ∀ {Δ Γ} {A : Ty Γ} (f : Sub Δ Γ) → Sub (Δ ∷ A [ f ]) (Γ ∷ A)
  f ↑ = (f ⊙ p ,, tr! Tm []-⊙ ν )

record StrictCwFStructure {i} (C : StrictCategory {i}) : Type (lsuc i) where
  field
    {{W}} : WildCwFStructure (s→w-cat C)
    
  open StrictCategory C using () renaming
    ( Ob-is-set  to Con-is-set
    ; Hom-is-set to Sub-is-set
    ) public
  open WildCwFStructure W public

  -- Additional truncation requirements
  field
    Ty-is-set : ∀ {Γ} → is-set (Ty Γ)
    Tm-is-set : ∀ {Γ} {σ : Ty Γ} → is-set (Tm σ)

-- Coercion
wild-of-strict : ∀ {i} {C : StrictCategory {i}}
                 → StrictCwFStructure C → WildCwFStructure (s→w-cat C)
wild-of-strict = StrictCwFStructure.W

{- Additional structure

Many of the following formulations follow after those in *Shallow Embedding of
Type Theory is Morally Correct* (Kaposi, Kovács, Kraus '18)

To avoid names getting too long we introduce the prefixes [w], [W] for "wild"
notions, and [s], [S] for "strict" ones.
-}
record PiStructure {i}
  {C : WildCategory {i}} (cwF : WildCwFStructure C) : Type (lsuc i)
  where
  open WildCwFStructure cwF public
  
  field
    ̂Π   : ∀ {Γ} (A : Ty Γ) (B : Ty (Γ ∷ A)) → Ty Γ
    ̂λ   : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ∷ A)} (b : Tm B) → Tm (̂Π A B)
    app : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ∷ A)} (f : Tm (̂Π A B)) → Tm B

    ̂Π-β : ∀ {Γ} {A} {B : Ty (Γ ∷ A)} (b : Tm B) → app (̂λ b) == b
    ̂Π-η : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ∷ A)} {f : Tm (̂Π A B)} → ̂λ (app f) == f

    -- Substitution rules
    ̂Π-[] : ∀ {Δ Γ} {A B} {f : Sub Δ Γ}
           → (̂Π A B) [ f ] == ̂Π (A [ f ]) (B [ f ↑ ])

    ̂λ-[] : ∀ {Δ Γ} {A} {B : Ty (Γ ∷ A)} {b : Tm B} {f : Sub Δ Γ}
           → (̂λ b) [ f ]ₜ == ̂λ (b [ f ↑ ]ₜ) [ Tm ↓ ̂Π-[] ]

  -- If we must talk about actually applying functions
  _`_ : ∀ {Γ} {A : Ty Γ} {B} (f : Tm (̂Π A B)) (a : Tm A)
        → Tm (B [ id ,, a [ id ]ₜ ])
  f ` a = (app f) [ id ,, a [ id ]ₜ ]ₜ

--record SigmaStructure {i}
