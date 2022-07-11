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

open WildCwFStructure cwf
open PiStructure pistr
open SigmaStructure sigmastr
open UnitStructure unitstr
open UStructure ustr

SCT : ℕ → Con
[_]-fillers : (h : ℕ) → Ty (SCT h)
M_at : (h h⁺ : ℕ) → ⦃ h ≤ h⁺ ⦄ → Ty (SCT h⁺)
M[_,_,_]_at : (i h t : ℕ) → is-shape i h t → (h⁺ : ℕ) → ⦃ h < h⁺ ⦄
              → Ty (SCT h⁺)

M-unc_at : (s : Shape) (h⁺ : ℕ) → ⦃ height s < h⁺ ⦄ → Ty (SCT h⁺)
M-unc ((i , h , t) , iS) at h⁺ = M[ i , h , t ] iS at h⁺

M⃗[_,_,_] : (i h t : ℕ) (iS : is-shape i h t)
            → ∀ {m} (f : Hom i m )
            → (hᵢ⁺ : ℕ) → ⦃ uᵢ : h < hᵢ⁺ ⦄
            → (hₒ⁺ : ℕ) → ⦃ uₒ : height ([ i , h , t ]∩[ m , f ] iS) < hₒ⁺ ⦄
            → Tm (M[ i , h , t ] iS at hᵢ⁺)
            → Tm (M-unc ([ i , h , t ]∩[ m , f ] iS) at hₒ⁺)

SCT O = ◆
SCT (1+ h) = SCT h ∷ [ h ]-fillers

[ h ]-fillers = M h at h ⦃ lteE ⦄ ̂→ U

M O at h⁺ = ̂⊤
M (1+ h) at .(1+ h) ⦃ inl idp ⦄ =
  M[ 1+ h , h , Hom-size (1+ h) h ] (full-shape (1+ h) h lteS) at (1+ h)
M (1+ h) at (1+ h⁺) ⦃ inr u ⦄ = M (1+ h) at h⁺ ⦃ <S→≤ u ⦄ ⁺

M[ i , h , 1+ t ] iS at .(1+ h) ⦃ ltS ⦄ =
  ̂Σ[ x ∈ prev-M ] {!x!}
  where
    prev-M : Ty (SCT (1+ h))
    prev-M = M[ i , h , t ] (shape-from-next-t iS) at (1+ h)

    M⃗-int : (i h t : ℕ) (iS : is-shape i h t) {m : ℕ} (f : Hom i m )
             → let ∩-hcond = ≤→<→< (height-of-∩ i h t m f iS) ltS
               in Tm (M[ i , h , t ] iS at (1+ h)
                      ̂→ M-unc ([ i , h , t ]∩[ m , f ] iS) at (1+ h) ⦃ ∩-hcond ⦄)
    M⃗-int i h t iS {m} f = ̂λ {!!}

M[ i , h , 1+ t ] iS at (1+ h⁺) ⦃ ltSR u ⦄ =
  M[ i , h , 1+ t ] iS at h⁺ ⦃ u ⦄ ⁺
M[ i , 1+ h , O ] iS at h⁺ ⦃ u ⦄ =
  M[ i , h , Hom-size i h ] (shape-from-next-h iS) at h⁺ ⦃ <-trans ltS u ⦄
M[ i , O , O ] iS at h⁺ = ̂⊤

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
           → M[ i , h , t ] iS at h⁺ [ π [ h⁺ ]-fillers ]
             == M[ i , h , t ] iS at (1+ h⁺)
  M-at-S i h (1+ t) iS .(1+ h) ⦃ ltS ⦄ ⦃ u' ⦄ = {!!}
  M-at-S i h (1+ t) iS (1+ h⁺) ⦃ ltSR u ⦄ ⦃ u' ⦄ =
    M[ i , h , 1+ t ] iS at (1+ h⁺) ⦃ ltSR u ⦄ ⁺
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

M⃗[ i , h , 1+ t ] iS {m} f hᵢ⁺ ⦃ uᵢ ⦄ (1+ ∩-height) ⦃ ltS ⦄ x = {!!}
M⃗[ i , h , 1+ t ] iS {m} f hᵢ⁺ ⦃ uᵢ ⦄ (1+ hₒ⁺) ⦃ ltSR uₒ ⦄ x =
  tr Tm
     (M-unc-at-S ([ i , h , 1+ t ]∩[ m , f ] iS) hₒ⁺ ⦃ uₒ ⦄ ⦃ ltSR uₒ ⦄)
     (M⃗[ i , h , 1+ t ] iS {m} f hᵢ⁺ hₒ⁺ ⦃ uₒ ⦄ x ⁺ₜ)
M⃗[ i , 1+ h , O ] iS f hᵢ⁺ hₒ⁺ x =
  M⃗[ i , h , Hom-size i h ] (shape-from-next-h iS) f hᵢ⁺ ⦃ _ ⦄ hₒ⁺ x
M⃗[ i , O , O ] iS f hᵢ⁺ hₒ⁺ x = ̂*
