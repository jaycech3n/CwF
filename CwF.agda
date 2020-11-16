{-# OPTIONS --without-K #-}

{--- Categories with families ---

Formulated as generalized algebraic theories following Dybjer ("Internal Type
Theory", 1996) and others.

To make equational reasoning and simplification easier we tend to follow the
following rules of thumb:

  1. Use explicit transports instead of the PathOver construct.
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
    ; Hom to Sub ) public
  
  field
    ◆ : Con
    ◆-is-terminal : is-terminal {{C}} ◆
  
  infixl 40 _[_] _[_]ₜ
  field
    Ty    : Con → Type i
    _[_]  : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
    
    []-id : ∀ {Γ} {σ : Ty Γ} → σ [ id ] == σ
          
    []-◦ : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε} {σ : Ty Ε}
         → σ [ g ◦ f ] == σ [ g ] [ f ]

    Tm   : ∀ {Γ} (σ : Ty Γ) → Type i
    _[_]ₜ : ∀ {Γ Δ} {σ : Ty Δ} → Tm σ → (f : Sub Γ Δ) → Tm (σ [ f ])

    []ₜ-id : ∀ {Γ} {σ : Ty Γ} {t : Tm σ} → tr Tm []-id (t [ id ]ₜ) == t

    []ₜ-◦ : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε} {σ} {t : Tm σ}
          → tr Tm []-◦ (t [ g ◦ f ]ₜ) == t [ g ]ₜ [ f ]ₜ

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
      
      []ₜ-◦' : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε} {σ} {t : Tm σ}
             → tr Tm (! []-◦) (t [ g ]ₜ [ f ]ₜ) == t [ g ◦ f ]ₜ
      []ₜ-◦' {Γ} {Δ} {Ε} {f} {g} {σ} {t} =
        tr!=-if-=tr (! ([]ₜ-◦ {Γ} {Δ} {Ε} {f} {g} {σ} {t}))
      
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
       → p ◦ (f ,, t) == f

    βν : ∀ {Δ Γ} {f : Sub Δ Γ} {σ : Ty Γ} {t : Tm (σ [ f ])}
       → ν [ f ,, t ]ₜ == tr Tm []-◦ (tr Tm (σ [= ! βp ]) t)
             
    ,,η : ∀ {Γ} {σ : Ty Γ} → (p {Γ} {σ} ,, ν {Γ} {σ}) == id

    ,,-◦ : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε}
             {σ : Ty Ε} {t : Tm (σ [ g ])}
         → (g ,, t) ◦ f == (g ◦ f ,, tr Tm (! []-◦) (t [ f ]ₜ))

  private
    module definitions where
      {- Exhanging transport and substitution -}
      tr-,, : ∀ {Γ Δ} {σ : Ty Γ} {σ' : Ty (Γ ∷ σ)}
                {f : Sub Δ Γ} {t : Tm (σ [ p ])} {t' : Tm (σ [ f ])}
                (eq : σ [ p ] == σ')
            → tr Tm eq t [ f ,, t' ]ₜ
              == tr Tm (ap _[ f ,, t' ] eq) (t [ f ,, t' ]ₜ)
      tr-,, idp = idp
      
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
      
      {- Uniqueness of comprehension -}
      ,,-uniq : ∀ {Δ Γ} {f : Sub Δ Γ} {σ : Ty Γ} {t : Tm (σ [ f ])}
                  (ϕ : Sub Δ (Γ ∷ σ))
                  (pϕ : p ◦ ϕ == f)
                  (νϕ : ν [ ϕ ]ₜ == tr Tm []-◦ (tr Tm (! (σ [= pϕ ])) t))
              → ϕ == (f ,, t)
      ,,-uniq {f = f} {σ = σ} {t = t} ϕ pϕ νϕ =
        ϕ            =⟨ ! idl ⟩
        id ◦ ϕ       =⟨ ! ,,η |in-ctx (_◦ ϕ) ⟩
        (p ,, ν) ◦ ϕ =⟨ ,,-◦ ⟩
        (p ◦ ϕ ,, tr Tm (! []-◦) (ν [ ϕ ]ₜ))
          =⟨ ,,-eq pϕ (νϕ |in-ctx (tr Tm (σ [= pϕ ]) ∘ (tr Tm (! []-◦)))) ⟩
        (f ,, tr Tm (σ [= pϕ ])
                 (tr Tm (! []-◦) (tr Tm []-◦ (tr Tm (! (σ [= pϕ ])) t))))
          =⟨ ,,-eq-last
               ( (tr-!-tr []-◦ |in-ctx (tr Tm (σ [= pϕ ])))
               ∙ tr-tr-! (σ [= pϕ ])) ⟩
        (f ,, t) =∎

      {- Weakening

      Given A : Ty Γ and f : Sub Δ Γ we get the weakening (f ↑ A) of f by A that
      intuitively acts as f does, and leaves the "free variable x : A" alone.
      This diagram commutes:

                          f ↑ A
                 Δ ∷ A[f] -----> Γ ∷ A
          p {A[f]} |               | p {A}
                   v               v
                   Δ ------------> Γ
                           f
      -}
      _↑_ : ∀ {Δ Γ} (f : Sub Δ Γ) (A : Ty Γ) → Sub (Δ ∷ A [ f ]) (Γ ∷ A)
      f ↑ A = (f ◦ p ,, tr Tm (! []-◦) (ν {_} {A [ f ]}))

      ↑-comm : ∀ {Δ Γ} {A : Ty Γ} {f : Sub Δ Γ} → p ◦ (f ↑ A) == f ◦ p
      ↑-comm = βp

      {-
      Given f : Sub Δ Γ, A : Ty Γ, and a : Tm A, we have the two "single-step"
      compositions from Δ to Γ ∷ A:

               (add a[f])
            Δ -----------> Δ ∷ A[f]
          f |                | f ↑ A
            v                v
            Γ -----------> Γ ∷ A
                (add a)

      where (add t) = (id ,, t [ id ]ₜ). There is also a direct substitution,
      which is just (f ,, a [ f ]ₜ).  We show that the two compositions are both
      equal to the direct substitution, which implies that the compositions are
      equal.

      The first is easy:
      -}
      ,,-◦-join : ∀ {Δ Γ} {A : Ty Γ} (f : Sub Δ Γ) (a : Tm A)
                → (id ,, a [ id ]ₜ) ◦ f == (f ,, (a [ f ]ₜ))
      ,,-◦-join f a =
        (id ,, a [ id ]ₜ) ◦ f =⟨ ,,-◦ ⟩
        (id ◦ f ,, tr Tm (! []-◦) (a [ id ]ₜ [ f ]ₜ)) =⟨ ,,-eq-last []ₜ-◦' ⟩
        (id ◦ f ,, a [ id ◦ f ]ₜ) =⟨ ,,-eq idl ([]ₜ-eq idl) ⟩
        (f ,, (a [ f ]ₜ)) =∎

      -- The second is a bit more work. We use the universal property ,,-uniq,
      -- and have to prove a somewhat lengthy reduction.
      p-↑-,, : ∀ {Δ Γ} {A : Ty Γ} (f : Sub Δ Γ) (a : Tm A)
             → p ◦ (f ↑ A) ◦ (id ,, a [ f ]ₜ [ id ]ₜ) == f
      p-↑-,, f a = ! ass
                 ∙ (↑-comm |in-ctx (_◦ (id ,, a [ f ]ₜ [ id ]ₜ)))
                 ∙ ass
                 ∙ (βp |in-ctx (f ◦_))
                 ∙ idr

      private
        module technical {Δ Γ : Con} {A : Ty Γ} {f : Sub Δ Γ} {a : Tm A} where
          lemma : ν [ f ◦ p ,, tr Tm (! []-◦) ν ]ₜ [ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ
                  == a [ p ]ₜ [ f ↑ A ]ₜ [ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ
          lemma =
            ν [ f ◦ p ,, tr Tm (! []-◦) ν ]ₜ [ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ
              =⟨ βν ∙ ! (tr-∙ (A [= ! βp ]) []-◦ (tr Tm (! []-◦) ν))
               |in-ctx (_[ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ) ⟩
            tr Tm ((A [= ! βp ]) ∙ []-◦) (tr Tm (! []-◦) ν)
             [ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ
              =⟨ ! (tr-∙ (! []-◦) ((A [= ! βp ]) ∙ []-◦) ν)
               |in-ctx (_[ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ) ⟩
            tr Tm (! []-◦ ∙ (A [= ! βp ]) ∙ []-◦) ν [ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ
              =⟨ tr-,, (! []-◦ ∙ (A [= ! βp ]) ∙ []-◦) ⟩
            tr Tm
               (ap _[ id ,, a [ f ]ₜ [ id ]ₜ ] (! []-◦ ∙ (A [= ! βp ]) ∙ []-◦))
               (ν [ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ)
              =⟨ βν
               |in-ctx (tr Tm (ap _[ id ,, a [ f ]ₜ [ id ]ₜ ] _)) ⟩
            tr Tm
               (ap _[ id ,, a [ f ]ₜ [ id ]ₜ ] (! []-◦ ∙ (A [= ! βp ]) ∙ []-◦))
               (tr Tm []-◦ (tr Tm ((A [ f ]) [= ! βp ]) (a [ f ]ₜ [ id ]ₜ)))
              =⟨ ( []ₜ-eq (! βp)
                 |in-ctx ((tr Tm (ap _[ id ,, a [ f ]ₜ [ id ]ₜ ]
                            (! []-◦ ∙ (A [= ! βp ]) ∙ []-◦))) ∘
                          (tr Tm []-◦)))
               ∙ ( []ₜ-◦
                 |in-ctx (tr Tm (ap _[ id ,, a [ f ]ₜ [ id ]ₜ ]
                             (! []-◦ ∙ (A [= ! βp ]) ∙ []-◦)))) ⟩
            tr Tm
               (ap _[ id ,, a [ f ]ₜ [ id ]ₜ ] (! []-◦ ∙ (A [= ! βp ]) ∙ []-◦))
               (a [ f ]ₜ [ p ]ₜ [ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ)
              =⟨ ! (tr-,, (! []-◦ ∙ (A [= ! βp ]) ∙ []-◦)) ⟩
            tr Tm (! []-◦ ∙ (A [= ! βp ]) ∙ []-◦) (a [ f ]ₜ [ p ]ₜ)
             [ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ
              =⟨ tr-∙ (! []-◦) ((A [= ! βp ]) ∙ []-◦) (a [ f ]ₜ [ p ]ₜ)
               ∙ tr-∙ (A [= ! βp ]) []-◦ _
               ∙ ([]ₜ-◦' |in-ctx (tr Tm []-◦) ∘ (tr Tm (A [= ! βp ])))
               ∙ ( []ₜ-eq (! βp) |in-ctx (tr Tm []-◦))
               ∙ []ₜ-◦
               |in-ctx _[ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ ⟩
            a [ p ]ₜ [ f ↑ A ]ₜ [ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ =∎
            
          calc : ν [ (f ↑ A) ◦ (id ,, a [ f ]ₜ [ id ]ₜ) ]ₜ
                 == a [ p ]ₜ [ (f ↑ A) ◦ (id ,, a [ f ]ₜ [ id ]ₜ) ]ₜ
          calc =
            ν [ (f ↑ A) ◦ (id ,, a [ f ]ₜ [ id ]ₜ) ]ₜ
              =⟨ =tr!-if-tr= []ₜ-◦ ⟩
            tr Tm (! []-◦)
             (ν [ _ ,, tr Tm (! []-◦) ν ]ₜ [ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ)
              =⟨ lemma |in-ctx (tr Tm (! []-◦)) ⟩
            tr Tm (! []-◦) (a [ p ]ₜ [ f ↑ A ]ₜ [ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ)
              =⟨ []ₜ-◦' ⟩
            a [ p ]ₜ [ (f ↑ A) ◦ (id ,, a [ f ]ₜ [ id ]ₜ) ]ₜ =∎

          calc' : tr Tm []-◦ (tr Tm (! (A [= p-↑-,, f a ])) (a [ f ]ₜ))
                  == a [ p ]ₜ [ (f ↑ A) ◦ (id ,, a [ f ]ₜ [ id ]ₜ) ]ₜ
          calc' =
            tr Tm []-◦ (tr Tm (! (A [= p-↑-,, f a ])) (a [ f ]ₜ))
              =⟨ tr!=-if-=tr (! ([]ₜ-eq (p-↑-,, f a))) |in-ctx (tr Tm []-◦) ⟩
            tr Tm []-◦ (a [ p ◦ (f ↑ A) ◦ (id ,, a [ f ]ₜ [ id ]ₜ) ]ₜ)
              =⟨ []ₜ-◦ ⟩
            a [ p ]ₜ [ (f ↑ A) ◦ (id ,, a [ f ]ₜ [ id ]ₜ) ]ₜ =∎

      ν-↑-,, : ∀ {Δ Γ} {A : Ty Γ} (f : Sub Δ Γ) (a : Tm A)
             → ν [ (f ↑ A) ◦ (id ,, a [ f ]ₜ [ id ]ₜ) ]ₜ
               == tr Tm []-◦ (tr Tm (! (A [= p-↑-,, f a ])) (a [ f ]ₜ))
      ν-↑-,, {A = A} f a = technical.calc ∙ ! technical.calc'

      ◦-,,-join : ∀ {Δ Γ} {A : Ty Γ} (f : Sub Δ Γ) (a : Tm A)
                → (f ↑ A) ◦ (id ,, a [ f ]ₜ [ id ]ₜ) == (f ,, (a [ f ]ₜ))
      ◦-,,-join {A = A} f a =
        (f ↑ A) ◦ (id ,, a [ f ]ₜ [ id ]ₜ)
          =⟨ ,,-uniq ((f ↑ A) ◦ (id ,, a [ f ]ₜ [ id ]ₜ))
                     (p-↑-,, f a) (ν-↑-,, f a) ⟩
        (f ,, a [ f ]ₜ) =∎

      ◦-,,-exch : ∀ {Δ Γ} {A : Ty Γ} (f : Sub Δ Γ) (a : Tm A)
                  → (id ,, a [ id ]ₜ) ◦ f == (f ↑ A) ◦ (id ,, a [ f ]ₜ [ id ]ₜ)
      ◦-,,-exch f a = ,,-◦-join f a  ∙ ! (◦-,,-join f a)

      {- Substitution in dependent types and terms -}
      infix 40 _[[_]] _[[_]]ₜ

      _[[_]] : ∀ {Γ} {A : Ty Γ} (B : Ty (Γ ∷ A)) (a : Tm A) → Ty Γ
      B [[ a ]] = B [ id ,, a [ id ]ₜ ]

      _[[_]]ₜ : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ∷ A)} (b : Tm B) (a : Tm A)
              → Tm (B [[ a ]])
      b [[ a ]]ₜ = b [ id ,, a [ id ]ₜ ]ₜ

      -- "Exchange"-type law for substitutions
      []-[[]] : ∀ {Δ Γ} {A : Ty Γ} {B : Ty (Γ ∷ A)} {f : Sub Δ Γ} {a : Tm A}
              → B [ f ↑ A ] [[ a [ f ]ₜ ]] == B [[ a ]] [ f ]

      []-[[]] {Δ} {Γ} {A} {B} {f} {a} =
        B [ f ↑ A ] [[ a [ f ]ₜ ]] =⟨ ! []-◦ ⟩
        B [ (f ↑ A) ◦ (id ,, a [ f ]ₜ [ id ]ₜ) ] =⟨ B [= ! (◦-,,-exch f a) ] ⟩
        B [ (id ,, a [ id ]ₜ) ◦ f ] =⟨ []-◦ ⟩
        B [ id ,, a [ id ]ₜ ] [ f ] =∎

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
               → StrictCwFStructure C
               → WildCwFStructure (s→w-cat C)
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
