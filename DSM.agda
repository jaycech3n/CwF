{-# OPTIONS --without-K #-}

{--- Decidable subsets of morphisms in well presented semicategories ---}

open import SuitableSemicategory

module DSM {ℓ}
  {Ob : Type ℓ}
  ⦃ C : LocallyFiniteSemicategoryOn Ob ⦄
  (_≟-Ob_ : has-dec-eq Ob) where

open LocallyFiniteSemicategoryOn C


Mor : Type ℓ
Mor = Σ[ x ∈ Ob ] Σ[ y ∈ Ob ] Hom x y

DSM : Type ℓ
DSM = Mor → Bool

-- Empty subset
Ø : DSM
Ø _ = false

add-arrow : Mor → DSM → DSM
add-arrow (u , v , g) σ (x , y , f) =
  if (x ≟-Ob u)
     (λ{ idp →
         if (y ≟-Ob v)
            (λ{ idp → True (f ≟-Hom g)})
            (λ no → σ (x , y , f)) })
     (λ no → σ (x , y , f))

_∩_ : DSM → DSM → DSM
(σ ∩ σ') f = σ f and σ' f
