{-# OPTIONS --without-K #-}

{--- Categories with families ---

Formulated as generalized algebraic theories following Dybjer ("Internal Type
Theory", 1996) and others.

To make equational reasoning and simplification easier we tend to follow the
following rules of thumb:

  1. Use explicit transports instead of the `PathOver` construct.
  2. Use repeated transports along paths, as opposed to transporting along a
     single concatenated path.

These may be broken as necessary. ---}

module CwF where

open import Category renaming
  ( [_] to ∥_∥
  ; wild-of-strict to s→w-cat
  ) public

{- Basic CwF structures -}
record TyTmStructure {i} (C : WildCategory {i}) : Type (lsuc i) where
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
    
    []-id : ∀ {Γ} {σ : Ty Γ} → σ [ id ] == σ
          
    []-⊙ : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε} {σ : Ty Ε}
           → σ [ g ⊙ f ] == σ [ g ] [ f ]

    Tm   : ∀ {Γ} (σ : Ty Γ) → Type i
    _[_]ₜ : ∀ {Γ Δ} {σ : Ty Δ} → Tm σ → (f : Sub Γ Δ) → Tm (σ [ f ])

    []ₜ-id : ∀ {Γ} {σ : Ty Γ} {t : Tm σ} → tr Tm []-id (t [ id ]ₜ) == t

    []ₜ-⊙ : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε} {σ} {t : Tm σ}
            → tr Tm []-⊙ (t [ g ⊙ f ]ₜ) == t [ g ]ₜ [ f ]ₜ

  private
    module definitions where
      {- Equality of types and terms -}
      infix 40 _[=_]
      _[=_] : ∀ {Δ Γ} {f f' : Sub Δ Γ} (σ : Ty Γ)
              → f == f' → σ [ f ] == σ [ f' ]
      _[=_] σ = ap (σ [_])

      []ₜ-eq : ∀ {Δ Γ} {f f' : Sub Δ Γ} {σ : Ty Γ} {t : Tm σ} (p : f == f')
               → tr Tm (σ [= p ]) (t [ f ]ₜ) == t [ f' ]ₜ
      []ₜ-eq idp = idp
      
  open definitions public

record WildCwFStructure {i} (C : WildCategory {i}) : Type (lsuc i) where
  field {{T}} : TyTmStructure C
  open TyTmStructure T public
  
  infixl 30 _,,_
  field
    _∷_  : (Γ : Con) (σ : Ty Γ) → Con
    p    : ∀ {Γ} {σ : Ty Γ} → Sub (Γ ∷ σ) Γ
    ν    : ∀ {Γ} {σ : Ty Γ} → Tm (σ [ p ])
    _,,_ : ∀ {Γ Δ} {σ : Ty Γ} (f : Sub Δ Γ) (t : Tm (σ [ f ])) → Sub Δ (Γ ∷ σ)

    -- The universal property of comprehensions is given by the following β- and
    -- η-rules.
    βp : ∀ {Δ Γ} {f : Sub Δ Γ} {σ : Ty Γ} {t : Tm (σ [ f ])}
         → p ⊙ (f ,, t) == f

    βν : ∀ {Δ Γ} {f : Sub Δ Γ} {σ : Ty Γ} {t : Tm (σ [ f ])}
         → ν [ f ,, t ]ₜ == tr Tm []-⊙ (tr Tm (σ [= ! βp ]) t)
             
    ,,η : ∀ {Γ} {σ : Ty Γ} → (p {Γ} {σ} ,, ν {Γ} {σ}) == id

    ,,-⊙ : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε}
             {σ : Ty Ε} {t : Tm (σ [ g ])}
           → (g ,, t) ⊙ f == (g ⊙ f ,, tr Tm (! []-⊙) (t [ f ]ₜ))

  private
    module definitions where
      {- Equality of substitutions -}
      ,,-eq : ∀ {Γ Δ} {σ : Ty Γ}
                {f f' : Sub Δ Γ} {t : Tm (σ [ f ])} {t' : Tm (σ [ f' ])}
                (eq₁ : f == f') (eq₂ : tr Tm (σ [= eq₁ ]) t == t')
              → (f ,, t) == (f' ,, t')
      ,,-eq idp idp = idp

      ,,-eq-init : ∀ {Γ Δ} {σ : Ty Γ} {f f' : Sub Δ Γ} {t : Tm (σ [ f ])}
                     (eq : f == f')
                   → (f ,, t) == (f' ,, tr Tm (σ [= eq ]) t)
      ,,-eq-init idp = idp

      ,,-eq-last : ∀ {Γ Δ} {σ : Ty Γ} {f : Sub Δ Γ} {t t' : Tm (σ [ f ])}
                     (eq : t == t')
                   → (f ,, t) == (f ,, t')
      ,,-eq-last idp = idp

      {- Weakening

      Given `A : Ty Γ` and `f : Sub Δ Γ` we get the weakening `f ↑ A` of `f` by
      `A` that intuitively acts as `f` does, and leaves the "free variable
      `x : A`" alone. This diagram commutes:

                          f ↑ A
                 Δ ∷ A[f] -----> Γ ∷ A
          p {A[f]} |               | p {A}
                   v               v
                   Δ ------------> Γ
                           f
      -}
      _↑_ : ∀ {Δ Γ} (f : Sub Δ Γ) (A : Ty Γ) → Sub (Δ ∷ A [ f ]) (Γ ∷ A)
      f ↑ A = (f ⊙ p ,, tr Tm (! []-⊙) (ν {_} {A [ f ]}))

      ↑-comm : ∀ {Δ Γ} {A : Ty Γ} {f : Sub Δ Γ} → p ⊙ (f ↑ A) == f ⊙ p
      ↑-comm = βp

      -- Somewhat technical equalities; not sure which I'll need yet.
      -- Note that the definitions in this module are currently not used.
      module rewrites {Δ Γ} {f : Sub Δ Γ} {A : Ty Γ} where
        ν[↑] : ν [ f ↑ A ]ₜ
               == tr Tm []-⊙ (tr Tm (A [= ! βp ]) (tr Tm (! []-⊙) ν))
        ν[↑] = βν

        ↑-eq : {t : Tm (A [ f ] [ id ])}
             → (f ↑ A)
               == (p ⊙ (f ↑ A) ,, tr Tm (A [= ! βp ]) (tr Tm (! []-⊙) ν))
        ↑-eq {t} = ,,-eq-init (! ↑-comm)

        ↑-subst-eq : {t : Tm (A [ f ] [ id ])}
                   → (f ↑ A) ⊙ (id ,, t)
                     == (  f
                        ,, tr Tm (A [= ass ∙ ap (f ⊙_) βp ∙ idr ])
                            (tr Tm (! []-⊙) (tr Tm (! []-⊙) ν [ id ,, t ]ₜ))
                        )
        ↑-subst-eq {t} =
          (f ⊙ p ,, tr Tm (! []-⊙) ν) ⊙ (id ,, t)
          =⟨ ,,-⊙ ⟩
          ((f ⊙ p) ⊙ (id ,, t) ,, tr Tm (! []-⊙) (tr Tm (! []-⊙) ν [ id ,, t ]ₜ))
          =⟨ ,,-eq-init (ass ∙ ap (f ⊙_) βp ∙ idr) ⟩
          _
          =∎

        calc1 : {a : Tm A} →
          a [ f ]ₜ [ p ]ₜ [ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ
          == tr Tm []-⊙ (tr Tm (A [ f ] [= ! βp ]) (a [ f ]ₜ [ id ]ₜ))
        calc1 {a} =
          a [ f ]ₜ [ p ]ₜ [ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ
          =⟨ ! []ₜ-⊙ ⟩
          tr Tm []-⊙ (a [ f ]ₜ [ p ⊙ (id ,, a [ f ]ₜ [ id ]ₜ) ]ₜ)
          =⟨ ! ([]ₜ-eq (! βp)) |in-ctx (tr Tm []-⊙) ⟩
          tr Tm []-⊙ (tr Tm (A [ f ] [= ! βp ]) (a [ f ]ₜ [ id ]ₜ))
          =∎

      -- Substitution in dependent types and terms
      infix 40 _[[_]] _[[_]]ₜ

      _[[_]] : ∀ {Γ} {A : Ty Γ} (B : Ty (Γ ∷ A)) (a : Tm A) → Ty Γ
      B [[ a ]] = B [ id ,, a [ id ]ₜ ]

      _[[_]]ₜ : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ∷ A)} (b : Tm B) (a : Tm A)
                → Tm (B [[ a ]])
      b [[ a ]]ₜ = b [ id ,, a [ id ]ₜ ]ₜ


      {- "Exchange"-type law for substitution extension and composition.
         Given f : Sub Δ Γ and A : Ty Γ and a : Tm A, we have two 
         "single-step" ways to go from Δ to Γ ∷ A, and they end up being
         equal:

                        (add a)
                   Δ -----------> Δ ∷ A[f]
                 f |               | f ↑ A
                   v               v
                   Γ -----------> Γ ∷ A
                       (add a)
      -}

      ,,-⊙-join : ∀ {Δ Γ} {A : Ty Γ} (f : Sub Δ Γ) (a : Tm A)
                → (id ,, a [ id ]ₜ) ⊙ f == (f ,, (a [ f ]ₜ))
      ,,-⊙-join {Γ} {Δ} {A} f a =
        ((id ,, a [ id ]ₜ) ⊙ f)
        =⟨ ,,-⊙  {f = f} {g = id} {t = a [ id ]ₜ} ⟩
        (id ⊙ f ,, tr Tm (! []-⊙) (a [ id ]ₜ [ f ]ₜ))
        =⟨ {!undo the transport!} ⟩
        (id ⊙ f ,, a [ id ⊙ f ]ₜ)
        =⟨ {!idl!} ⟩
        (f ,, (a [ f ]ₜ))
        =∎

      ⊙-,,-join : ∀ {Δ Γ} {A : Ty Γ} (f : Sub Δ Γ) (a : Tm A)
                  → (f ↑ A) ⊙ (id ,, a [ f ]ₜ [ id ]ₜ) == (f ,, (a [ f ]ₜ))
      ⊙-,,-join {Γ} {Δ} {A} f a =
        (f ↑ A) ⊙ (id ,, a [ f ]ₜ [ id ]ₜ)
        =⟨ {!,,-⊙  {f = f} {g = id} {t = a [ id ]ₜ}!} ⟩
--        {!!}
--        =⟨ {!!} ⟩
--        {!!}
--        =⟨ {!!} ⟩
--        {!!}
        (f ,, (a [ f ]ₜ))
        =∎ 



      ⊙-,,-exch : ∀ {Δ Γ} {A : Ty Γ} (f : Sub Δ Γ) (a : Tm A)
                  → (id ,, a [ id ]ₜ) ⊙ f == (f ↑ A) ⊙ (id ,, a [ f ]ₜ [ id ]ₜ)
      ⊙-,,-exch f a = ,,-⊙-join f a  ∙ ! (⊙-,,-join f a)



      -- "Exchange"-type law for substitutions
      []-[[]] : ∀ {Δ Γ} {A : Ty Γ} {B : Ty (Γ ∷ A)} {f : Sub Δ Γ} {a : Tm A}
                → B [ f ↑ A ] [[ a [ f ]ₜ ]] == B [[ a ]] [ f ]

      []-[[]] {Δ} {Γ} {A} {B} {f} {a} =
        B [ f ↑ A ] [[ a [ f ]ₜ ]] =⟨ ! []-⊙ ⟩
        B [ (f ↑ A) ⊙ (id ,, a [ f ]ₜ [ id ]ₜ) ] =⟨ B [= eq ] ⟩
        B [ (id ,, a [ id ]ₜ) ⊙ f ] =⟨ []-⊙ ⟩
        B [ id ,, a [ id ]ₜ ] [ f ] =∎
        where
        eq : (f ↑ A) ⊙ (id ,, a [ f ]ₜ [ id ]ₜ) == (id ,, a [ id ]ₜ) ⊙ f
        eq = {!!}


      [[]]-[] : ∀ {Δ Γ} {A : Ty Γ} {B : Ty (Γ ∷ A)} {f : Sub Δ Γ} {a : Tm A}
                → B [[ a ]] [ f ] == B [ f ↑ A ] [[ a [ f ]ₜ ]]
      [[]]-[] = ! []-[[]]

  open definitions public

record StrictCwFStructure {i} (C : StrictCategory {i}) : Type (lsuc i) where
  field {{W}} : WildCwFStructure (s→w-cat C)
  
  open WildCwFStructure W hiding (T) public
  open StrictCategory C using () renaming
    ( Ob-is-set  to Con-is-set
    ; Hom-is-set to Sub-is-set
    ) public

  -- Additional truncation requirements
  field
    Ty-is-set : ∀ {Γ} → is-set (Ty Γ)
    Tm-is-set : ∀ {Γ} {σ : Ty Γ} → is-set (Tm σ)

{- Coercion -}
wild-of-strict : ∀ {i} {C : StrictCategory {i}}
                   {{T : TyTmStructure (s→w-cat C)}}
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
           → (̂Π A B) [ f ] == ̂Π (A [ f ]) (B [ f ↑ A ])

    ̂λ-[] : ∀ {Δ Γ} {A} {B : Ty (Γ ∷ A)} {b : Tm B} {f : Sub Δ Γ}
           → (̂λ b) [ f ]ₜ == ̂λ (b [ f ↑ A ]ₜ) [ Tm ↓ ̂Π-[] ]

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
           → (̂Σ A B) [ f ] == ̂Σ (A [ f ]) (B [ f ↑ A ])
           
    ،-[] : ∀ {Δ Γ} {A : Ty Γ} {B : Ty (Γ ∷ A)}
           {a : Tm A} {b : Tm (B [[ a ]])} {f : Sub Δ Γ}
           → (a ، b) [ f ]ₜ == (a [ f ]ₜ ، tr Tm [[]]-[] (b [ f ]ₜ))
             [ Tm ↓ ̂Σ-[] ]
