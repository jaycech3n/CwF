{-# OPTIONS --without-K #-}

{- Categories with families

Formulated as generalized algebraic theories following Dybjer ("Internal Type
Theory", 1996) and others.
-}

module CwF where

open import Category renaming
  ( [_] to ∥_∥
  ; wild-of-strict to s→w-cat
  ) public

{- Basic CwF structures

To make equational reasoning and simplification easier we tend to follow the
following rules of thumb:

1. Use explicit transports instead of the `PathOver` construct.
2. Use repeated transports along paths, as opposed to transporting along a
   single concatenated path.

These may be broken as necessary.
-}
record WildCwFStructure {i} (C : WildCategory {i}) : Type (lsuc i) where
  open WildCategory C renaming
    ( Ob to Con
    ; Hom to Sub
    ) public
  
  field
    ◆ : Con
    ◆-is-terminal : is-terminal {{C}} ◆
  
  infixl 40 _[_] _[_]ₜ
  field
    Ty    : Con → Type i
    _[_]  : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
    
    []-id : ∀ {Γ} {σ : Ty Γ} → (σ [ id ]) == σ
          
    []-⊙ : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε} {σ : Ty Ε}
           → (σ [ g ⊙ f ]) == (σ [ g ] [ f ])

    Tm   : ∀ {Γ} (σ : Ty Γ) → Type i
    _[_]ₜ : ∀ {Γ Δ} {σ : Ty Δ} → Tm σ → (f : Sub Γ Δ) → Tm (σ [ f ])

    []ₜ-id : ∀ {Γ} {σ : Ty Γ} {t : Tm σ} → t [ id ]ₜ == tr Tm (! []-id) t

    []ₜ-⊙ : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε} {σ} {t : Tm σ}
            → t [ g ⊙ f ]ₜ == tr Tm (! []-⊙) (t [ g ]ₜ [ f ]ₜ)

  -- Comprehensions: context extension and projections
  infixl 30 _,,_
  field
    _∷_  : (Γ : Con) (σ : Ty Γ) → Con
    p    : ∀ {Γ} {σ : Ty Γ} → Sub (Γ ∷ σ) Γ
    ν    : ∀ {Γ} {σ : Ty Γ} → Tm (σ [ p ])
    _,,_ : ∀ {Γ Δ} {σ : Ty Γ} (f : Sub Δ Γ) (t : Tm (σ [ f ])) → Sub Δ (Γ ∷ σ)

    -- The universal property of comprehensions is given by the following β- and
    -- η-rules.
    p-,, : ∀ {Δ Γ} {f : Sub Δ Γ} {σ : Ty Γ} {t : Tm (σ [ f ])}
           → p ⊙ (f ,, t) == f

    ν-,, : ∀ {Δ Γ} {f : Sub Δ Γ} {σ : Ty Γ} {t : Tm (σ [ f ])}
           → ν [ f ,, t ]ₜ == tr Tm []-⊙ (tr (Tm ∘ (σ [_])) (! p-,,) t)
             
    ,,-id : ∀ {Γ} {σ : Ty Γ} → (p {Γ} {σ} ,, ν {Γ} {σ}) == id

    ,,-⊙ : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε}
             {σ : Ty Ε} {t : Tm (σ [ g ])}
           → (g ,, t) ⊙ f == (g ⊙ f ,, tr Tm (! []-⊙) (t [ f ]ₜ))

  {- Substitutions and their properties -}
  module _ where
    -- Manipulating transports
    []ₜ-id' : ∀ {Γ} {σ : Ty Γ} {t : Tm σ} → tr Tm []-id (t [ id ]ₜ) == t
    []ₜ-id' = move-tr-!-l []ₜ-id

    []ₜ-⊙' : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε} {σ} {t : Tm σ}
             → tr Tm []-⊙ (t [ g ⊙ f ]ₜ) == t [ g ]ₜ [ f ]ₜ
    []ₜ-⊙' = move-tr-!-l []ₜ-⊙

    -- Equality for substitutions
    ,,-eq : ∀ {Γ Δ} {σ : Ty Γ}
              {f f' : Sub Δ Γ} {t : Tm (σ [ f ])} {t' : Tm (σ [ f' ])}
              (eq₁ : f == f') (eq₂ : tr (Tm ∘ (σ [_])) eq₁ t == t')
            → (f ,, t) == (f' ,, t')
    ,,-eq idp idp = idp

    ,,-eq-l : ∀ {Γ Δ} {σ : Ty Γ} {f f' : Sub Δ Γ} {t : Tm (σ [ f ])}
                (eq : f == f')
              → (f ,, t) == (f' ,, tr (Tm ∘ (σ [_])) eq t)
    ,,-eq-l idp = idp

    ,,-eq-r : ∀ {Γ Δ} {σ : Ty Γ} {f : Sub Δ Γ} {t t' : Tm (σ [ f ])}
                (eq : t == t')
              → (f ,, t) == (f ,, t')
    ,,-eq-r idp = idp
    
    []ₜ-eq : ∀ {Δ Γ} {f f' : Sub Δ Γ} {σ : Ty Γ} {t : Tm σ} (eq : f == f')
           → tr (Tm ∘ (σ [_])) eq (t [ f ]ₜ) == t [ f' ]ₜ
    []ₜ-eq idp = idp

    {- Given `A : Ty Γ` and `f : Sub Δ Γ` we get the lifted substitution `f ↑`
    -- that acts as `f` does, and leaves the "free variable x : A" alone.
    -- This diagram commutes:
                          f ↑
                Δ ∷ A[f] -----> Γ ∷ A
         p {A[f]} |               | p {A}
                  v               v
                  Δ ------------> Γ
                          f
    -}
    _↑ : ∀ {Δ Γ} {A : Ty Γ} (f : Sub Δ Γ) → Sub (Δ ∷ A [ f ]) (Γ ∷ A)
    _↑ {_} {_} {A} f = (f ⊙ p ,, tr Tm (! []-⊙) (ν {_} {A [ f ]}))

    _↑-comm : ∀ {Δ Γ} {A : Ty Γ} {f : Sub Δ Γ} → p {_} {A} ⊙ (f ↑) == f ⊙ p
    _↑-comm = p-,,

    -- Substitution in dependent types and terms
    infix 40 _[[_]] _[[_]]ₜ

    _[[_]] : ∀ {Γ} {A : Ty Γ} (B : Ty (Γ ∷ A)) (a : Tm A) → Ty Γ
    B [[ a ]] = B [ id ,, a [ id ]ₜ ]

    _[[_]]ₜ : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ∷ A)} (b : Tm B) (a : Tm A)
              → Tm (B [[ a ]])
    b [[ a ]]ₜ = b [ id ,, a [ id ]ₜ ]ₜ

    -- Somewhat technical proof of an equality we need
    private
      module _ {Δ Γ} {f : Sub Δ Γ} {A : Ty Γ} {a : Tm A} where
        private
          eq = ass ∙ ap (f ⊙_) p-,, ∙ idr
          
        module _ where
          private
            ν* = tr Tm (! []-⊙) ν
            ν+ = ν* [ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ

          _↑-lem :
            (f ↑) ⊙ (id ,, a [ f ]ₜ [ id ]ₜ) ==
            (f ,, tr (Tm ∘ (A [_])) eq (tr Tm (! []-⊙) ν+))

          _↑-lem =
            (f ⊙ p ,, tr Tm (! []-⊙) ν) ⊙ (id ,, a [ f ]ₜ [ id ]ₜ)
            =⟨ ,,-⊙ ⟩
            ((f ⊙ p) ⊙ (id ,, a [ f ]ₜ [ id ]ₜ) ,, tr Tm (! []-⊙) ν+)
            =⟨ ,,-eq-l eq ⟩
            _
            =∎

        tr-ν-lemma :
          tr Tm (! []-⊙) (tr Tm (! []-⊙) ν [ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ)
          == a [ (f ⊙ p) ⊙ (id ,, a [ f ]ₜ [ id ]ₜ) ]ₜ
        tr-ν-lemma =
          move-tr-l {p = []-⊙} (
            {!!} ∙ (! []ₜ-⊙')
          )
        
        rearrangement-lemma :
          tr (Tm ∘ _[_] A) eq
            (tr Tm (! []-⊙)
              (tr Tm (! []-⊙) ν [ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ))
          == a [ f ]ₜ

        rearrangement-lemma =
          move-tr-!-l {p = eq} (
            tr Tm (! []-⊙)
              (tr Tm (! []-⊙) ν [ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ)
            =⟨ tr-ν-lemma ⟩
            a [ (f ⊙ p) ⊙ (id ,, a [ f ]ₜ [ id ]ₜ) ]ₜ
            =⟨ ! ([]ₜ-eq (! eq)) ⟩
            _
            =∎
          )

    -- "Exchange"-type law for substitutions
    []-[[]] : ∀ {Δ Γ} {A : Ty Γ} {B : Ty (Γ ∷ A)} {f : Sub Δ Γ} {a : Tm A}
              → B [ f ↑ ] [[ a [ f ]ₜ ]] == B [[ a ]] [ f ]

    []-[[]] {Δ} {Γ} {A} {B} {f} {a} =
      B [ f ⊙ p ,, tr Tm (! []-⊙) ν ] [[ a [ f ]ₜ ]] =⟨ ! []-⊙ ⟩
      B [ (f ⊙ p ,, _) ⊙ (id ,, a [ f ]ₜ [ id ]ₜ) ] =⟨ eq |in-ctx (B [_]) ⟩
      B [ (id ,, a [ id ]ₜ) ⊙ f ] =⟨ []-⊙ ⟩
      B [ id ,, a [ id ]ₜ ] [ f ] =∎
      where
      eq = 
        (f ⊙ p ,, tr Tm (! []-⊙) ν) ⊙ (id ,, a [ f ]ₜ [ id ]ₜ)
        =⟨ ,,-⊙ ⟩
        ((f ⊙ p) ⊙ (id ,, _) ,, _)
        =⟨ ,,-eq-l (ass ∙ (p-,, |in-ctx (f ⊙_)) ∙ idr) ⟩
        (f ,, _)
        =⟨ ,,-eq-r rearrangement-lemma ⟩
        ((f ,, a [ f ]ₜ))
        =⟨ ,,-eq (! idl) ([]ₜ-eq (! idl)) ⟩
        (id ⊙ f ,, a [ id ⊙ f ]ₜ )
        =⟨ ,,-eq idp []ₜ-⊙ ⟩
        (id ⊙ f ,, tr Tm (! []-⊙) (a [ id ]ₜ [ f ]ₜ))
        =⟨ ! ,,-⊙ ⟩
        (id ,, a [ id ]ₜ) ⊙ f
        =∎

    [[]]-[] : ∀ {Δ Γ} {A : Ty Γ} {B : Ty (Γ ∷ A)} {f : Sub Δ Γ} {a : Tm A}
              → B [[ a ]] [ f ] == B [ f ↑ ] [[ a [ f ]ₜ ]]
    [[]]-[] = ! []-[[]]


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

Many of the following formulations loosely follow those in *Shallow Embedding of
Type Theory is Morally Correct* (Kaposi, Kovács, Kraus '18).
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
        → Tm (B [[ a ]])
  f ` a = (app f) [[ a ]]ₜ

record SigmaStructure {i}
  {C : WildCategory {i}} (cwF : WildCwFStructure C) : Type (lsuc i)
  where
  open WildCwFStructure cwF public
  field
    ̂Σ   : ∀ {Γ} (A : Ty Γ) (B : Ty (Γ ∷ A)) → Ty Γ
    _،_ : ∀ {Γ} {A} {B : Ty (Γ ∷ A)} (a : Tm A) (b : Tm (B [[ a ]]))
          → Tm (̂Σ A B)
    π1 : ∀ {Γ} {A} {B : Ty (Γ ∷ A)} → Tm (̂Σ A B) → Tm A    
    π2 : ∀ {Γ} {A} {B : Ty (Γ ∷ A)} (p : Tm (̂Σ A B)) → Tm (B [[ π1 p ]])

  field
    ،-π1 : ∀ {Γ} {A} {B : Ty (Γ ∷ A)} {a : Tm A} {b : Tm (B [[ a ]])}
           → π1 (a ، b) == a
           
    ،-π2 : ∀ {Γ} {A} {B : Ty (Γ ∷ A)} {a : Tm A} {b : Tm (B [[ a ]])}
           → π2 (a ، b) == b [ Tm ∘ (B [[_]]) ↓ ،-π1 ]
           
    ̂Σ-η : ∀ {Γ} {A} {B : Ty (Γ ∷ A)} {p : Tm (̂Σ A B)} → (π1 p ، π2 p) == p

  field
    ̂Σ-[] : ∀ {Δ Γ} {A B} {f : Sub Δ Γ}
           → (̂Σ A B) [ f ] == ̂Σ (A [ f ]) (B [ f ↑ ])
           
    ،-[] : ∀ {Δ Γ} {A : Ty Γ} {B : Ty (Γ ∷ A)}
           {a : Tm A} {b : Tm (B [[ a ]])} {f : Sub Δ Γ}
           → (a ، b) [ f ]ₜ == (a [ f ]ₜ ، tr Tm [[]]-[] (b [ f ]ₜ))
             [ Tm ↓ ̂Σ-[] ]
