{-# OPTIONS --without-K --termination-depth=3 #-}

open import SuitableSemicategories
open import CwF

module SCT {ℓ}
  ⦃ I : SuitableSemicategory ⦄
  ( C : WildCategory {ℓ} )
  ( cwf      : WildCwFStructure C )
  ( pistr    : PiStructure cwf    )
  ( sigmastr : SigmaStructure cwf )
  ( unitstr  : UnitStructure cwf  )
  ( ustr     : UStructure cwf     )
  where

open import ShapedSieves
open SuitableSemicategory I

open WildCwFStructure cwf renaming (_◦_ to _◦ᶜ_)
open PiStructure pistr
open SigmaStructure sigmastr
open UnitStructure unitstr
open UStructure ustr

SCT : ℕ → Con
[_]-fillers-at : (h h⁺ : ℕ) → ⦃ h ≤ h⁺ ⦄ → Ty (SCT h⁺)
M_at : (h h⁺ : ℕ) → ⦃ h ≤ h⁺ ⦄ → Ty (SCT h⁺)
M[_,_,_]_at : (i h t : ℕ) → is-shape i h t → (h⁺ : ℕ) → ⦃ h < h⁺ ⦄
              → Ty (SCT h⁺)

M-unc_at : (s : Shape) (h⁺ : ℕ) → ⦃ height s < h⁺ ⦄ → Ty (SCT h⁺)
M-unc ((i , h , t) , iS) at h⁺ = M[ i , h , t ] iS at h⁺

M[_,_,_]_↾ :
  (i h t : ℕ) (iS : is-shape i h t)
  → {m : ℕ} (f : Hom i m )
  → (h⁺ : ℕ) → ⦃ u : h < h⁺ ⦄
  → let M       = M[ i , h , t ] iS at h⁺
        SCT∷M   = SCT h⁺ ∷ M
        ∩-hcond = ≤→<→< (height-of-∩ i h t iS f) u
    in Sub SCT∷M
           (SCT∷M ∷ M-unc ([ i , h , t ]∩[ m , f ] iS)
                      at h⁺ ⦃ ∩-hcond ⦄ [ π M ])

M↾-is-section :
  (i h t : ℕ) (iS : is-shape i h t)
  → {m : ℕ} (f : Hom i m )
  → (h⁺ : ℕ) → ⦃ u : h < h⁺ ⦄
  → let M       = M[ i , h , t ] iS at h⁺
        SCT∷M   = SCT h⁺ ∷ M
        ∩-hcond = ≤→<→< (height-of-∩ i h t iS f) u
        M-∩     = M-unc ([ i , h , t ]∩[ m , f ] iS)
                    at h⁺ ⦃ ∩-hcond ⦄ [ π M ]
    in (π M-∩) ◦ᶜ (M[ i , h , t ] iS ↾ f h⁺) == id


SCT O = ◆
SCT (1+ h) = SCT h ∷ [ h ]-fillers-at h ⦃ lteE ⦄

[ h ]-fillers-at h⁺ = M h at h⁺ ̂→ U

[_]-fillers : (h : ℕ) → Ty (SCT h)
[ h ]-fillers = [ h ]-fillers-at h ⦃ lteE ⦄

M O at h⁺ = ̂⊤
M (1+ h) at .(1+ h) ⦃ inl idp ⦄ =
  M[ 1+ h , h , Hom-size (1+ h) h ] (full-shape (1+ h) h lteS) at (1+ h)
M (1+ h) at (1+ h⁺) ⦃ inr u ⦄ = M (1+ h) at h⁺ ⦃ <S→≤ u ⦄ ʷ [ h⁺ ]-fillers

module matching-objs where
  M-wk-eq : ∀ h h⁺ → ⦃ u : h ≤ h⁺ ⦄
            → M h at h⁺ ⦃ u ⦄ ʷ [ h⁺ ]-fillers == M h at (1+ h⁺) ⦃ lteSR u ⦄
  M-wk-eq O h⁺ = ̂⊤-[]
  M-wk-eq (1+ h) .(1+ h) ⦃ inl idp ⦄ = idp
  M-wk-eq (1+ h) h⁺ ⦃ inr _ ⦄ = idp

open matching-objs

module fillers where
  [_]-fillers-wk-eq :
    (h h⁺ : ℕ) ⦃ u : h ≤ h⁺ ⦄
    → [ h ]-fillers-at h⁺ ʷ [ h⁺ ]-fillers
      == [ h ]-fillers-at (1+ h⁺) ⦃ lteSR u ⦄
  [ h ]-fillers-wk-eq h⁺ ⦃ u ⦄ =
    ̂→-[]
    ∙ (M-wk-eq h h⁺ |in-ctx (_̂→ U ʷ [ h⁺ ]-fillers))
    ∙ (U-[] |in-ctx (M h at (1+ h⁺) ⦃ lteSR u ⦄ ̂→_))

  -- (A h of-SCT h⁺) is the filler Aₕ in context SCT h⁺ which has initial segment
  -- (SCT h , Aₕ : [ h ]-fillers).
  A_of-SCT :
    (h h⁺ : ℕ) ⦃ u : h < h⁺ ⦄ → Tm {SCT h⁺} ([ h ]-fillers-at h⁺ ⦃ inr u ⦄)
  A h of-SCT .(1+ h) ⦃ ltS ⦄ =
    tr Tm ([ h ]-fillers-wk-eq h ⦃ lteE ⦄) (υ [ h ]-fillers)
  A h of-SCT (1+ h⁺) ⦃ ltSR u ⦄ =
    tr Tm ([ h ]-fillers-wk-eq h⁺ ⦃ inr u ⦄) (A h of-SCT h⁺ ⦃ u ⦄ ʷₜ [ h⁺ ]-fillers)

open fillers

M[ i , h , 1+ t ] iS at .(1+ h) ⦃ ltS ⦄ =
  ̂Σ[ x ∈ prev-M ]
    let
      [t]-restriction : Tm (M-unc ([ i , h , t ]∩[ h , [t] ] prev-iS) at (1+ h)
                             ʷ prev-M)
      [t]-restriction = tr Tm (ʷ-[[]] (prev-M-∩ ʷ prev-M) _ x)
                           (M↾-̂λ ⃗[ π prev-M ]ₜ ` x)
    in {!Aₕ ` [t]-restriction!}
  where
    prev-iS : is-shape i h t
    prev-iS = shape-from-next-t iS

    prev-M : Ty (SCT (1+ h))
    prev-M = M[ i , h , t ] prev-iS at (1+ h)

    [t] = Hom[ i , h ]# (t , S≤→< (tcond iS))
    instance height-∩<Sh = ≤→<→< (height-of-∩ i h t prev-iS [t]) ltS

    prev-M-∩ : Ty (SCT (1+ h))
    prev-M-∩ = M-unc ([ i , h , t ]∩[ h , [t] ] prev-iS) at (1+ h)
      -- Should be able to just norm↑ or norm↓ the restriction here, and this should work?

    -- The restriction map as an internal lambda
    M↾-̂λ : Tm (prev-M ̂→ prev-M-∩)
    M↾-̂λ = ̂λ (tm (prev-M-∩ ʷ prev-M)
              of (M[ i , h , t ] prev-iS ↾ [t] (1+ h))
                 (M↾-is-section i h t prev-iS [t] (1+ h)))
M[ i , h , 1+ t ] iS at (1+ h⁺) ⦃ ltSR u ⦄ =
  M[ i , h , 1+ t ] iS at h⁺ ⦃ u ⦄ ʷ [ h⁺ ]-fillers
M[ i , 1+ h , O ] iS at h⁺ ⦃ u ⦄ =
  M[ i , h , Hom-size i h ] (shape-from-next-h iS) at h⁺ ⦃ <-trans ltS u ⦄
M[ i , O , O ] iS at h⁺ = ̂⊤

{- Should (morally, maybe modulo the (i, 1+h, 0) case) have the fact that
     M[ i , h , t ] ... at (1+ h⁺) == M[ i , h , t ] ... at h⁺ ʷ [ h⁺ ]-fillers,
   but do we need it in this generality? -}

module eq-lemmas where
  M-lvl-cond-irr : (i h t : ℕ) (iS : is-shape i h t)
                 → (h⁺ : ℕ) (u u' : h < h⁺)
                 → M[ i , h , t ] iS at h⁺ ⦃ u ⦄
                   == M[ i , h , t ] iS at h⁺ ⦃ u' ⦄
  M-lvl-cond-irr i h t iS h⁺ u u' with <-has-all-paths u u'
  ... | idp = idp

  M-unc-lvl-cond-irr : (s : Shape) (h⁺ : ℕ) {u u' : height s < h⁺}
                       → M-unc s at h⁺ ⦃ u ⦄ == M-unc s at h⁺ ⦃ u' ⦄
  M-unc-lvl-cond-irr ((i , h , t) , iS) h⁺ {u} {u'} =
    M-lvl-cond-irr i h t iS h⁺ u u'

  M-at-S : (i h t : ℕ) (iS : is-shape i h t) (h⁺ : ℕ)
           ⦃ u : h < h⁺ ⦄ ⦃ u' : h < 1+ h⁺ ⦄
           → M[ i , h , t ] iS at h⁺ ʷ [ h⁺ ]-fillers
             == M[ i , h , t ] iS at (1+ h⁺)
  M-at-S i h (1+ t) iS .(1+ h) ⦃ ltS ⦄ ⦃ u' ⦄ = {!!}
  M-at-S i h (1+ t) iS (1+ h⁺) ⦃ ltSR u ⦄ ⦃ u' ⦄ =
    M[ i , h , 1+ t ] iS at (1+ h⁺) ⦃ ltSR u ⦄ ʷ [ 1+ h⁺ ]-fillers
    =⟨ idp ⟩
    M[ i , h , 1+ t ] iS at (2+ h⁺) ⦃ ltSR (ltSR u) ⦄
    =⟨ ! (M-lvl-cond-irr i h (1+ t) iS (2+ h⁺) u' (ltSR (ltSR u))) ⟩
    M[ i , h , 1+ t ] iS at (2+ h⁺) ⦃ u' ⦄
    =∎
  M-at-S i (1+ h) O iS h⁺ ⦃ u ⦄ ⦃ u' ⦄ =
    M-at-S i h (Hom-size i h) (shape-from-next-h iS) h⁺
      ⦃ <-trans ltS u ⦄ ⦃ <-trans ltS u' ⦄
  M-at-S i O O iS h⁺ = ̂⊤-[]

  M-unc-at-S : (s : Shape) (h⁺ : ℕ)
               ⦃ u : height s < h⁺ ⦄ ⦃ u' : height s < 1+ h⁺ ⦄
               → M-unc s at h⁺ [ π [ h⁺ ]-fillers ] == M-unc s at (1+ h⁺)
  M-unc-at-S ((i , h , t) , iS) h⁺ ⦃ u ⦄ ⦃ u' ⦄ =
    M-at-S i h t iS h⁺ ⦃ u ⦄ ⦃ u' ⦄

open eq-lemmas

M[ i , h , 1+ t ] iS ↾ f h⁺ = {!!}
M[ i , 1+ h , O ] iS ↾ f h⁺ ⦃ u ⦄ =
  {!M[ i , h , Hom-size i h ] (shape-from-next-h iS) ↾ f h⁺ ⦃ <-trans ltS u ⦄!}
M[ i , O , O ] iS ↾ f h⁺ = id ,, tr Tm (! ̂⊤-[] ∙ []-◦) ̂*

M↾-is-section i h (1+ t) iS f h⁺ = {!!}
M↾-is-section i (1+ h) O iS f h⁺ = {!!}
M↾-is-section i O O iS f h⁺ = βπ

{-
SCT-proj : ∀ {h⁺ h} → h ≤ h⁺ → Sub (SCT h⁺) (SCT h)
SCT-proj {.h} {h} (inl idp) = id
SCT-proj {.(1+ h)} {h} (inr ltS) = π [ h ]-fillers
SCT-proj {1+ h⁺} {h} (inr (ltSR u)) = SCT-proj (inr u) ◦ᶜ π [ h⁺ ]-fillers

M⃗[ i , h , 1+ t ] iS {m} f hᵢ ⦃ uᵢ ⦄ (1+ ∩-height) ⦃ ltS ⦄ = {!!}
M⃗[ i , h , 1+ t ] iS {m} f hᵢ ⦃ uᵢ ⦄ (1+ hₒ) ⦃ ltSR uₒ ⦄ = {!!}
M⃗[ i , 1+ h , O ] iS f hᵢ ⦃ uᵢ ⦄ hₒ =
  M⃗[ i , h , Hom-size i h ] (shape-from-next-h iS) f hᵢ ⦃ <-trans ltS uᵢ ⦄ hₒ
M⃗[ i , O , O ] iS f hᵢ hₒ ⦃ hₒmax = hₒmax ⦄ = SCT-proj hₒmax ᵂ[ ̂⊤ , ̂⊤ , ̂⊤-[] ]
-}
