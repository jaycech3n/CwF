{-# OPTIONS --without-K #-}

{--- Categories with families

We formalize CwFs as generalized algebraic theories following Dybjer ("Internal
Type Theory", 1996) and others.

To make equational reasoning and simplification easier we tend to follow the
following rules of thumb (which may, however, be broken as needed):

  1. Use explicit transports instead of the PathOver construct.
  2. Use repeated transports along paths, instead of transporting along a single
     concatenated path.
-}

module CwF where

open import Categories public


{- Basic CwF structures -}

record TyTmStructure {ℓ} (C : WildCategory {ℓ}) : Type (lsuc ℓ) where
  open WildCategory C
    renaming
    ( Ob to Con
    ; Hom to Sub )
    public

  field
    ◆ : Con
    ◆-is-terminal : is-terminal ⦃ semi-of-wild-cat ⦃ C ⦄ ⦄ ◆

  infixl 40 _[_] _[_]ₜ
  field
    Ty    : Con → Type ℓ
    _[_]  : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
    []-id : ∀ {Γ} {A : Ty Γ} → A [ id ] == A
    []-◦  : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε} {A : Ty Ε} -- Greek capital
                                                             -- epsilon "\GE"
            → A [ g ◦ f ] == A [ g ] [ f ]

    Tm     : ∀ {Γ} (A : Ty Γ) → Type ℓ
    _[_]ₜ  : ∀ {Γ Δ} {A : Ty Δ} → Tm A → (f : Sub Γ Δ) → Tm (A [ f ])
    []ₜ-id : ∀ {Γ} {A : Ty Γ} {t : Tm A} → tr Tm []-id (t [ id ]ₜ) == t
    []ₜ-◦  : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε} {A : Ty Ε} {t : Tm A}
             → tr Tm []-◦ (t [ g ◦ f ]ₜ) == t [ g ]ₜ [ f ]ₜ

  private
    module definitions where

      {- Equality of types and terms -}

      infix 40 _[=_]

      _[=_] : ∀ {Δ Γ} {f f' : Sub Δ Γ} (A : Ty Γ)
              → f == f' → A [ f ] == A [ f' ]
      _[=_] A = ap (A [_])

      []ₜ-eq : ∀ {Δ Γ} {f f' : Sub Δ Γ} {A : Ty Γ} {t : Tm A} (p : f == f')
               → tr Tm (A [= p ]) (t [ f ]ₜ) == t [ f' ]ₜ
      []ₜ-eq idp = idp

      []ₜ-◦' : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε} {A} {t : Tm A}
               → tr Tm (! []-◦) (t [ g ]ₜ [ f ]ₜ) == t [ g ◦ f ]ₜ
      []ₜ-◦' {Γ} {Δ} {Ε} {f} {g} {A} {t} =
        ==tr-tr!== (! ([]ₜ-◦ {Γ} {Δ} {Ε} {f} {g} {A} {t}))

  open definitions public


record WildCwFStructure {ℓ} (C : WildCategory {ℓ}) : Type (lsuc ℓ) where
  field ⦃ T ⦄ : TyTmStructure C
  open TyTmStructure T public

  infixl 20 _∷_
  infixl 30 _,,_
  field
    _∷_ : (Γ : Con) (A : Ty Γ) → Con
    π    : ∀ {Γ} (A : Ty Γ) → Sub (Γ ∷ A) Γ
    υ    : ∀ {Γ} (A : Ty Γ) → Tm (A [ π A ])
    _,,_ : ∀ {Γ Δ} {A : Ty Γ} (f : Sub Δ Γ) (t : Tm (A [ f ])) → Sub Δ (Γ ∷ A)

    -- The universal property of comprehensions is given by the following β- and
    -- η-rules.

    βπ : ∀ {Δ Γ} {f : Sub Δ Γ} {A : Ty Γ} {t : Tm (A [ f ])}
         → π A ◦ (f ,, t) == f

    βυ : ∀ {Δ Γ} {f : Sub Δ Γ} {A : Ty Γ} {t : Tm (A [ f ])}
         → υ A [ f ,, t ]ₜ == tr Tm []-◦ (tr Tm (A [= ! βπ ]) t)

    ,,η : ∀ {Γ} {A : Ty Γ} → (π A ,, υ A) == id

    ,,-◦ : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε}
             {A : Ty Ε} {t : Tm (A [ g ])}
           → (g ,, t) ◦ f == (g ◦ f ,, tr Tm (! []-◦) (t [ f ]ₜ))

  private
    module definitions where

      {- Terms from sections -}

      tm_of : ∀ {Γ} (A : Ty Γ) (σ : Sub Γ (Γ ∷ A)) (p : π A ◦ σ == id) → Tm A
      tm A of σ p = tr Tm ((! []-◦) ∙ (A [= p ]) ∙ []-id) (υ A [ σ ]ₜ)

      {- Exhanging transport and substitution -}

      tr-,, : ∀ {Γ Δ} {A : Ty Γ} {A' : Ty (Γ ∷ A)}
                {f : Sub Δ Γ} {t : Tm (A [ π A ])} {t' : Tm (A [ f ])}
                (eq : A [ π A ] == A')
              → (tr Tm eq t) [ f ,, t' ]ₜ
                ==
                tr Tm (ap _[ f ,, t' ] eq) (t [ f ,, t' ]ₜ)
      tr-,, idp = idp

      {- Equality of substitutions -}

      ,,-eq : ∀ {Γ Δ} {A : Ty Γ}
                {f f' : Sub Δ Γ} {t : Tm (A [ f ])} {t' : Tm (A [ f' ])}
              → (eq : f == f')
              → tr Tm (A [= eq ]) t == t'
              → (f ,, t) == (f' ,, t')
      ,,-eq idp idp = idp

      ,,-eq-init : ∀ {Γ Δ} {A : Ty Γ} {f f' : Sub Δ Γ} {t : Tm (A [ f ])}
                   → (eq : f == f')
                   → (f ,, t) == (f' ,, tr Tm (A [= eq ]) t)
      ,,-eq-init idp = idp

      ,,-eq-last : ∀ {Γ Δ} {A : Ty Γ} {f : Sub Δ Γ} {t t' : Tm (A [ f ])}
                   → t == t'
                   → (f ,, t) == (f ,, t')
      ,,-eq-last idp = idp

      {- Uniqueness of comprehension -}

      ,,-uniq : ∀ {Δ Γ} {f : Sub Δ Γ} {A : Ty Γ} {t : Tm (A [ f ])}
                  (ϕ : Sub Δ (Γ ∷ A))
                  (πϕ : π A ◦ ϕ == f)
                  (υϕ : υ A [ ϕ ]ₜ == tr Tm []-◦ (tr Tm (! (A [= πϕ ])) t))
                → ϕ == (f ,, t)
      ,,-uniq {f = f} {A = A} {t = t} ϕ πϕ υϕ =
        ϕ

        =⟨ ! idl ⟩

          id ◦ ϕ

        =⟨ ! ,,η |in-ctx (_◦ ϕ) ⟩

          (π A ,, υ A) ◦ ϕ

        =⟨ ,,-◦ ⟩

          (π A ◦ ϕ ,, tr Tm (! []-◦) (υ A [ ϕ ]ₜ))

        =⟨ ,,-eq πϕ (υϕ |in-ctx (tr Tm (A [= πϕ ]) ∘ (tr Tm (! []-◦)))) ⟩

          (f ,, tr Tm (A [= πϕ ])
                      (tr Tm (! []-◦) (tr Tm []-◦ (tr Tm (! (A [= πϕ ])) t))))

        =⟨ ,,-eq-last
             ((tr!-tr []-◦ |in-ctx (tr Tm (A [= πϕ ]))) ∙ tr-tr! (A [= πϕ ])) ⟩

        (f ,, t)

        =∎

      {- Weakening substitutions

      Given A : Ty Γ and f : Sub Δ Γ, we get the weakening (f ↑ A) of f by A
      that, intuitively, acts as f does, and leaves the "free variable x : A"
      alone.  This diagram commutes:

                          f ↑ A
                 Δ ∷ A[f] -----> Γ ∷ A
          π (A[f]) |               | π A
                   ↓               ↓
                   Δ ------------> Γ
                           f
      -}

      _↑_ : ∀ {Δ Γ} (f : Sub Δ Γ) (A : Ty Γ) → Sub (Δ ∷ A [ f ]) (Γ ∷ A)
      f ↑ A = f ◦ π (A [ f ]) ,, tr Tm (! []-◦) (υ (A [ f ]))

      ↑-comm : ∀ {Δ Γ} {A : Ty Γ} {f : Sub Δ Γ} → π A ◦ (f ↑ A) == f ◦ π (A [ f ])
      ↑-comm = βπ

      -- Version of _↑_ with explicit equality
      _ᵂ[_,_,_] : ∀ {Δ Γ} (f : Sub Δ Γ) (B : Ty Δ) (A : Ty Γ) (p : A [ f ] == B)
                  → Sub (Δ ∷ B) (Γ ∷ A)
      _ᵂ[_,_,_] {Δ} {Γ} f B A p = tr (λ □ → Sub (Δ ∷ □) (Γ ∷ A)) p (f ↑ A)
        -- Could also copy the definition of _↑_ and fiddle around with
        -- heterogenous equalities?

      {- Given f : Sub Δ Γ, A : Ty Γ, and a : Tm A, we have the two "single-step"
      compositions from Δ to Γ ∷ A:

                add a[f]
            Δ -----------> Δ ∷ A[f]
          f |                | f ↑ A
            ↓                ↓
            Γ -----------> Γ ∷ A
                 add a

      where (add t) = (id ,, t [ id ]ₜ). There is also a direct substitution,
      which is just (f ,, a [ f ]ₜ).  We show that the two compositions are both
      equal to the direct substitution, which implies that the compositions are
      equal.

      The first is easy: -}

      ,,-◦-join : ∀ {Δ Γ} {A : Ty Γ} (f : Sub Δ Γ) (a : Tm A)
                  → (id ,, a [ id ]ₜ) ◦ f == (f ,, a [ f ]ₜ)
      ,,-◦-join f a =
        (id ,, a [ id ]ₜ) ◦ f

        =⟨ ,,-◦ ⟩

          (id ◦ f ,, tr Tm (! []-◦) (a [ id ]ₜ [ f ]ₜ))

        =⟨ ,,-eq-last []ₜ-◦' ⟩

          (id ◦ f ,, a [ id ◦ f ]ₜ)

        =⟨ ,,-eq idl ([]ₜ-eq idl) ⟩

        (f ,, (a [ f ]ₜ))

        =∎

      {- The second is a bit more work. We use the universal property ,,-uniq,
      and have to prove a somewhat lengthy reduction. -}

      π∘↑∘,, : ∀ {Δ Γ} {A : Ty Γ} (f : Sub Δ Γ) (a : Tm A)
               → π A ◦ (f ↑ A) ◦ (id ,, a [ f ]ₜ [ id ]ₜ) == f
      π∘↑∘,, f a = ! ass
                 ∙ (↑-comm |in-ctx (_◦ (id ,, a [ f ]ₜ [ id ]ₜ)))
                 ∙ ass
                 ∙ (βπ |in-ctx (f ◦_))
                 ∙ idr

      private
        module technical {Δ Γ : Con} {A : Ty Γ} {f : Sub Δ Γ} {a : Tm A} where
          lemma : υ A [ f ◦ π (A [ f ]) ,, tr Tm (! []-◦) (υ (A [ f ])) ]ₜ
                      [ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ
                  ==
                  a [ π A ]ₜ [ f ↑ A ]ₜ [ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ
          lemma =
            υ A [ f ◦ π (A [ f ]) ,, tr Tm (! []-◦) (υ (A [ f ])) ]ₜ
                [ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ

            =⟨ βυ ∙ ! (tr-∙ (A [= ! βπ ]) []-◦ (tr Tm (! []-◦) (υ (A [ f ]))))
             |in-ctx (_[ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ)
             ⟩

              (tr Tm ((A [= ! βπ ]) ∙ []-◦) (tr Tm (! []-◦) (υ (A [ f ]))))
                [ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ

            =⟨ ! (tr-∙ (! []-◦) ((A [= ! βπ ]) ∙ []-◦) (υ (A [ f ])))
             |in-ctx (_[ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ)
             ⟩

              (tr Tm (! []-◦ ∙ (A [= ! βπ ]) ∙ []-◦) (υ (A [ f ])))
                [ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ

            =⟨ tr-,, (! []-◦ ∙ (A [= ! βπ ]) ∙ []-◦) ⟩

              tr Tm
                 (ap _[ id ,, a [ f ]ₜ [ id ]ₜ ] (! []-◦ ∙ (A [= ! βπ ]) ∙ []-◦))
                 (υ (A [ f ]) [ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ)

            =⟨ βυ
             |in-ctx (tr Tm (ap _[ id ,, a [ f ]ₜ [ id ]ₜ ] _))
             ⟩

              tr Tm
                 (ap _[ id ,, a [ f ]ₜ [ id ]ₜ ] (! []-◦ ∙ (A [= ! βπ ]) ∙ []-◦))
                 (tr Tm []-◦ (tr Tm ((A [ f ]) [= ! βπ ]) (a [ f ]ₜ [ id ]ₜ)))

            =⟨ ( []ₜ-eq (! βπ)
                 |in-ctx (
                   (tr Tm (ap _[ id ,, a [ f ]ₜ [ id ]ₜ ]
                       (! []-◦ ∙ (A [= ! βπ ]) ∙ []-◦)))
                   ∘ (tr Tm []-◦)))
               ∙
               ( []ₜ-◦
                 |in-ctx (tr Tm (ap _[ id ,, a [ f ]ₜ [ id ]ₜ ]
                             (! []-◦ ∙ (A [= ! βπ ]) ∙ []-◦))))
             ⟩

              tr Tm
                 (ap _[ id ,, a [ f ]ₜ [ id ]ₜ ] (! []-◦ ∙ (A [= ! βπ ]) ∙ []-◦))
                 (a [ f ]ₜ [ π (A [ f ]) ]ₜ [ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ)

            =⟨ ! (tr-,, (! []-◦ ∙ (A [= ! βπ ]) ∙ []-◦)) ⟩

              (tr Tm (! []-◦ ∙ (A [= ! βπ ]) ∙ []-◦) (a [ f ]ₜ [ π (A [ f ]) ]ₜ))
                [ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ

            =⟨ tr-∙ (! []-◦) ((A [= ! βπ ]) ∙ []-◦) (a [ f ]ₜ [ π (A [ f ]) ]ₜ)
               ∙ tr-∙ (A [= ! βπ ]) []-◦ _
               ∙ ([]ₜ-◦' |in-ctx (tr Tm []-◦) ∘ (tr Tm (A [= ! βπ ])))
               ∙ ( []ₜ-eq (! βπ) |in-ctx (tr Tm []-◦))
               ∙ []ₜ-◦
             |in-ctx _[ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ
             ⟩

            a [ π A ]ₜ [ f ↑ A ]ₜ [ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ

            =∎

          calc : υ A [ (f ↑ A) ◦ (id ,, a [ f ]ₜ [ id ]ₜ) ]ₜ
                 ==
                 a [ π A ]ₜ [ (f ↑ A) ◦ (id ,, a [ f ]ₜ [ id ]ₜ) ]ₜ
          calc =
            υ A [ (f ↑ A) ◦ (id ,, a [ f ]ₜ [ id ]ₜ) ]ₜ
            =⟨ tr==-==tr! []ₜ-◦ ⟩
              tr Tm (! []-◦)
                (υ A [ _ ,, tr Tm (! []-◦) (υ (A [ f ])) ]ₜ [ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ)
            =⟨ lemma |in-ctx (tr Tm (! []-◦)) ⟩
              tr Tm (! []-◦) (a [ π A ]ₜ [ f ↑ A ]ₜ [ id ,, a [ f ]ₜ [ id ]ₜ ]ₜ)
            =⟨ []ₜ-◦' ⟩
            a [ π A ]ₜ [ (f ↑ A) ◦ (id ,, a [ f ]ₜ [ id ]ₜ) ]ₜ
            =∎

          calc' : tr Tm []-◦ (tr Tm (! (A [= π∘↑∘,, f a ])) (a [ f ]ₜ))
                  ==
                  a [ π A ]ₜ [ (f ↑ A) ◦ (id ,, a [ f ]ₜ [ id ]ₜ) ]ₜ
          calc' =
            tr Tm []-◦ (tr Tm (! (A [= π∘↑∘,, f a ])) (a [ f ]ₜ))
            =⟨ ==tr-tr!== (! ([]ₜ-eq (π∘↑∘,, f a))) |in-ctx (tr Tm []-◦) ⟩
              tr Tm []-◦ (a [ π A ◦ (f ↑ A) ◦ (id ,, a [ f ]ₜ [ id ]ₜ) ]ₜ)
            =⟨ []ₜ-◦ ⟩
            a [ π A ]ₜ [ (f ↑ A) ◦ (id ,, a [ f ]ₜ [ id ]ₜ) ]ₜ
            =∎

      υ-↑-,, : ∀ {Δ Γ} {A : Ty Γ} (f : Sub Δ Γ) (a : Tm A)
               → υ A [ (f ↑ A) ◦ (id ,, a [ f ]ₜ [ id ]ₜ) ]ₜ
                 ==
                 tr Tm []-◦ (tr Tm (! (A [= π∘↑∘,, f a ])) (a [ f ]ₜ))
      υ-↑-,, f a = technical.calc ∙ ! technical.calc'

      ◦-,,-join : ∀ {Δ Γ} {A : Ty Γ} (f : Sub Δ Γ) (a : Tm A)
                  → (f ↑ A) ◦ (id ,, a [ f ]ₜ [ id ]ₜ) == (f ,, (a [ f ]ₜ))
      ◦-,,-join {A = A} f a =
        (f ↑ A) ◦ (id ,, a [ f ]ₜ [ id ]ₜ)
        =⟨ ,,-uniq ((f ↑ A) ◦ (id ,, a [ f ]ₜ [ id ]ₜ))
                   (π∘↑∘,, f a) (υ-↑-,, f a) ⟩
        (f ,, a [ f ]ₜ)
        =∎

      ◦-,,-exch : ∀ {Δ Γ} {A : Ty Γ} (f : Sub Δ Γ) (a : Tm A)
                  → (id ,, a [ id ]ₜ) ◦ f == (f ↑ A) ◦ (id ,, a [ f ]ₜ [ id ]ₜ)
      ◦-,,-exch f a = ,,-◦-join f a  ∙ ! (◦-,,-join f a)

      {- Weakening types and terms -}

      infixl 40 _ʷ_ _ʷ̇ _ʷₜ_ _⁺

      _ʷ_ : ∀ {Γ} → Ty Γ → (A : Ty Γ) → Ty (Γ ∷ A)
      T ʷ A = T [ π A ]

      _ʷ̇  : ∀ {Γ} {A : Ty Γ} → Ty Γ → Ty (Γ ∷ A)
      _ʷ̇  {A = A} T = T ʷ A

      _⁺ : ∀ {Γ} (A : Ty Γ) → Ty (Γ ∷ A)
      A ⁺ = A ʷ A

      _ʷₜ_ : ∀ {Γ} {T : Ty Γ} → Tm T → (A : Ty Γ) → Tm (T ʷ A)
      t ʷₜ A = t [ π A ]ₜ

      {- Term substitution -}

      infix 40 _[[_]] _[[_]]ₜ

      _[[_]] : ∀ {Γ} {A : Ty Γ} (B : Ty (Γ ∷ A)) (a : Tm A) → Ty Γ
      B [[ a ]] = B [ id ,, a [ id ]ₜ ]

      _[[_]]ₜ : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ∷ A)} (b : Tm B) (a : Tm A)
                → Tm (B [[ a ]])
      b [[ a ]]ₜ = b [ id ,, a [ id ]ₜ ]ₜ

      -- Term substitution in a weakened type is trivial
      ʷ-[[]] : ∀ {Γ} (T A : Ty Γ) (a : Tm A) → T ʷ A [[ a ]] == T
      ʷ-[[]] T A a = ! []-◦ ∙ (T [= βπ ]) ∙ []-id

      -- "Commutativity" law
      []-[[]] : ∀ {Δ Γ} {A : Ty Γ} {B : Ty (Γ ∷ A)} {f : Sub Δ Γ} {a : Tm A}
                → B [ f ↑ A ] [[ a [ f ]ₜ ]] == B [[ a ]] [ f ]
      []-[[]] {Δ} {Γ} {A} {B} {f} {a} =
        B [ f ↑ A ] [[ a [ f ]ₜ ]]               =⟨ ! []-◦ ⟩
        B [ (f ↑ A) ◦ (id ,, a [ f ]ₜ [ id ]ₜ) ] =⟨ B [= ! (◦-,,-exch f a) ] ⟩
        B [ (id ,, a [ id ]ₜ) ◦ f ]              =⟨ []-◦ ⟩
        B [ id ,, a [ id ]ₜ ] [ f ]              =∎

      [[]]-[] : ∀ {Δ Γ} {A : Ty Γ} {B : Ty (Γ ∷ A)} {f : Sub Δ Γ} {a : Tm A}
                → B [[ a ]] [ f ] == B [ f ↑ A ] [[ a [ f ]ₜ ]]
      [[]]-[] = ! []-[[]]

  open definitions public


record StrictCwFStructure {ℓ} (C : StrictCategory {ℓ}) : Type (lsuc ℓ) where
  field ⦃ W ⦄ : WildCwFStructure (wild-of-strict-cat C)

  open WildCwFStructure W hiding (T) public
  open StrictCategory C using () renaming
    ( Ob-is-set  to Con-is-set
    ; Hom-is-set to Sub-is-set
    ) public

  -- Additional truncation requirements

  field
    Ty-is-set : ∀ {Γ} → is-set (Ty Γ)
    Tm-is-set : ∀ {Γ} {A : Ty Γ} → is-set (Tm A)


{- Coercion -}

wild-of-strict-cwf : ∀ {ℓ} {C : StrictCategory {ℓ}}
                       ⦃ T : TyTmStructure (wild-of-strict-cat C) ⦄
                     → StrictCwFStructure C
                     → WildCwFStructure (wild-of-strict-cat C)
wild-of-strict-cwf = StrictCwFStructure.W


{- Additional structure -}

-- Many of the following formulations loosely follow those in "Shallow Embedding
-- of Type Theory is Morally Correct" (Kaposi, Kovács, Kraus '18).

record PiStructure {ℓ}
  {C : WildCategory {ℓ}} (cwf : WildCwFStructure C) : Type (lsuc ℓ)
  where
  open WildCwFStructure cwf

  field
    ̂Π   : ∀ {Γ} (A : Ty Γ) (B : Ty (Γ ∷ A)) → Ty Γ
    ̂λ   : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ∷ A)} (b : Tm B) → Tm (̂Π A B)
    app : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ∷ A)} (f : Tm (̂Π A B)) → Tm B

    ̂Π-β : ∀ {Γ} {A} {B : Ty (Γ ∷ A)} (b : Tm B) → app (̂λ b) == b
    ̂Π-η : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ∷ A)} {f : Tm (̂Π A B)} → ̂λ (app f) == f

    -- Substitution

    ̂Π-[] : ∀ {Δ Γ} {A B} {f : Sub Δ Γ}
           → (̂Π A B) [ f ] == ̂Π (A [ f ]) (B [ f ↑ A ])

    ̂λ-[] : ∀ {Δ Γ} {A} {B : Ty (Γ ∷ A)} {b : Tm B} {f : Sub Δ Γ}
           → (̂λ b) [ f ]ₜ == ̂λ (b [ f ↑ A ]ₜ) [ Tm ↓ ̂Π-[] ]

  private
    module definitions where

      {- Function application -}

      _`_ : ∀ {Γ} {A : Ty Γ} {B}
            → (f : Tm (̂Π A B)) (a : Tm A)
            → Tm (B [[ a ]])
      f ` a = (app f) [[ a ]]ₜ

      {- Syntax -}

      ̂Π' : ∀ {Γ} (A : Ty Γ) (B : Tm (A [ π A ]) → Ty (Γ ∷ A)) → Ty Γ
      ̂Π' A B = ̂Π A (B (υ A))

      syntax ̂Π' A (λ x → B) = ̂Π[ x ∈ A ] B

      infixr 35 _̂→_
      _̂→_ : ∀ {Γ} (A B : Ty Γ) → Ty Γ
      A ̂→ B = ̂Π A (B [ π A ])

      {- Substitution -}

      ̂→-[] : ∀ {Δ Γ} {A B : Ty Γ} {f : Sub Δ Γ}
             → (A ̂→ B) [ f ] == (A [ f ] ̂→ B [ f ])
      ̂→-[] {_} {_} {A} {B} {f}
        = (̂Π A (B [ π A ])) [ f ]
        =⟨ ̂Π-[] ⟩ ̂Π (A [ f ]) (B [ π A ] [ f ↑ A ])
        =⟨ ! []-◦ |in-ctx (λ □ → ̂Π _ □) ⟩ ̂Π (A [ f ]) (B [ π A ◦ (f ↑ A) ])
        =⟨ ↑-comm |in-ctx (λ □ → ̂Π _ (B [ □ ])) ⟩ ̂Π (A [ f ]) (B [ f ◦ π (A [ f ]) ])
        =⟨ []-◦   |in-ctx (λ □ → ̂Π _ □) ⟩ ̂Π (A [ f ]) (B [ f ] [ π (A [ f ]) ]) =∎

      infixl 30 _⃗[_]ₜ
      _⃗[_]ₜ : ∀ {Δ Γ} {A B : Ty Γ}
              → (f : Tm (A ̂→ B)) (σ : Sub Δ Γ)
              → Tm (A [ σ ] ̂→ B [ σ ])
      f ⃗[ σ ]ₜ = tr Tm ̂→-[] (f [ σ ]ₜ)

      {- Weakening -}

      _⃗ʷₜ : ∀ {Γ} {A B C : Ty Γ} → Tm ((A ̂→ B) ʷ C) → Tm (A ʷ C ̂→ B ʷ C)
      f ⃗ʷₜ = tr Tm ̂→-[] f

  open definitions public


record SigmaStructure {ℓ}
  {C : WildCategory {ℓ}} (cwf : WildCwFStructure C) : Type (lsuc ℓ)
  where
  open WildCwFStructure cwf
  field
    ̂Σ   : ∀ {Γ} (A : Ty Γ) (B : Ty (Γ ∷ A)) → Ty Γ
    _،_ : ∀ {Γ} {A} {B : Ty (Γ ∷ A)} (a : Tm A) (b : Tm (B [[ a ]]))
          → Tm (̂Σ A B)
    ̂fst : ∀ {Γ} {A} {B : Ty (Γ ∷ A)} → Tm (̂Σ A B) → Tm A
    ̂snd : ∀ {Γ} {A} {B : Ty (Γ ∷ A)} (p : Tm (̂Σ A B)) → Tm (B [[ ̂fst p ]])

    -- Equations

    ،-̂fst : ∀ {Γ} {A} {B : Ty (Γ ∷ A)} {a : Tm A} {b : Tm (B [[ a ]])}
            → ̂fst (a ، b) == a

    ،-̂snd : ∀ {Γ} {A} {B : Ty (Γ ∷ A)} {a : Tm A} {b : Tm (B [[ a ]])}
            → ̂snd (a ، b) == b [ Tm ∘ (B [[_]]) ↓ ،-̂fst ]

    ̂Σ-η : ∀ {Γ} {A} {B : Ty (Γ ∷ A)} {p : Tm (̂Σ A B)} → (̂fst p ، ̂snd p) == p

    -- Substitution

    ̂Σ-[] : ∀ {Δ Γ} {A B} {f : Sub Δ Γ}
          → (̂Σ A B) [ f ] == ̂Σ (A [ f ]) (B [ f ↑ A ])

    ،-[] : ∀ {Δ Γ} {A : Ty Γ} {B : Ty (Γ ∷ A)}
           {a : Tm A} {b : Tm (B [[ a ]])} {f : Sub Δ Γ}
           → (a ، b) [ f ]ₜ
             == (a [ f ]ₜ ، tr Tm [[]]-[] (b [ f ]ₜ)) [ Tm ↓ ̂Σ-[] ]

  private
    module definitions where
      ̂Σ-syntax : ∀ {Γ} (A : Ty Γ) (B : Tm (A [ π A ]) → Ty (Γ ∷ A)) → Ty Γ
      ̂Σ-syntax A B = ̂Σ A (B (υ A))

      syntax ̂Σ-syntax A (λ x → B) = ̂Σ[ x ∈ A ] B

      infixl 35 _̂×_
      _̂×_ : ∀ {Γ} (A B : Ty Γ) → Ty Γ
      A ̂× B = ̂Σ A (B [ π A ])

      -- n-fold nonempty product

      _ˣ_ : ∀ {Γ} (A : Ty Γ) (n : ℕ) ⦃ O<n : O < n ⦄ → Ty Γ
      A ˣ (1+ O) = A
      A ˣ (1+ (1+ n)) = (A ˣ (1+ n)) ̂× A

  open definitions public


record UnitStructure {ℓ}
  {C : WildCategory {ℓ}} (cwf : WildCwFStructure C) : Type (lsuc ℓ)
  where
  open WildCwFStructure cwf

  field
    ̂⊤    : ∀ {Γ} → Ty Γ
    ̂*    : ∀ {Γ} → Tm {Γ} ̂⊤
    ̂⊤η   : ∀ {Γ} {t : Tm {Γ} ̂⊤} → t == ̂*
    ̂⊤-[] : ∀ {Γ Δ} {f : Sub Δ Γ} → ̂⊤ [ f ] == ̂⊤

  private
    module definitions where
      ̂*-[] : ∀ {Γ Δ} {f : Sub Δ Γ} {t :  Tm {Γ} ̂⊤} → t [ f ]ₜ == ̂* [ Tm ↓ ̂⊤-[] ]
      ̂*-[] = from-tr _ _ ̂⊤η


-- "Universe" of types. This is not the universe internalizing all types in Γ;
-- rather, a base type family.

record UStructure {ℓ}
  {C : WildCategory {ℓ}} (cwf : WildCwFStructure C) : Type (lsuc ℓ)
  where
  open WildCwFStructure cwf

  field
    U     : ∀ {Γ} → Ty Γ
    el    : ∀ {Γ} → Tm {Γ} U → Ty Γ
    U-[]  : ∀ {Γ Δ} {f : Sub Δ Γ} → U [ f ] == U
    el-[] : ∀ {Γ Δ} {f : Sub Δ Γ} {T : Tm {Γ} U}
            → (el T) [ f ] == el (tr Tm U-[] (T [ f ]ₜ))

  private
    module definitions where
      _↓ : ∀ {Γ Δ} {f : Sub Δ Γ} → Tm (U [ f ]) → Tm U
      _↓ = tr Tm U-[]

  open definitions public
