{-# OPTIONS --without-K --termination-depth=2 #-}

module bht.SCT where

open import CwF public
open import bht.NiceIndexCategory
open import bht.Sieves

module _ {i}
  ⦃ I : NiceIndexCategory {i} ⦄
  ( C : WildCategory {i} )
  ( cwf         : WildCwFStructure C )
  ( pistruct    : PiStructure cwf    )
  ( sigmastruct : SigmaStructure cwf )
  ( unitstruct  : UnitStructure cwf  )
  ( ustruct     : UStructure cwf     )
  where
  open NiceIndexCategory I
  open WildCwFStructure cwf
  open PiStructure pistruct
  open SigmaStructure sigmastruct
  open UnitStructure unitstruct
  open UStructure ustruct

  SCT : ℕ → Con
  Sk  : (b h t : ℕ) → is-sieve b h t → Ty (SCT (1+ h))

  Sk-unc  : (((_ , h , _) , _) : Sieve) → Ty (SCT (1+ h))
  Sk-unc ((b , h , t) , iS) = Sk b h t iS

  Sk→ : (b h t : ℕ) (iS : is-sieve b h t)
        {m : ℕ} (f : Hom m b)
        → Tm (Sk b h t iS)
        → Tm (Sk-unc ([ b , h , t ]∩[ m , f ] iS))

  -- M b is the "matching object" of the diagram induced by (SCT b).
  M   : (b : ℕ) → Ty (SCT b)
  M O = ̂⊤
  M (1+ b) = Sk (1+ b) b (Hom-size b (1+ b)) (is-sieve-bhtmax lteS)

  _-Fillers : (b : ℕ) → Ty (SCT b)
  b -Fillers = M b ̂→ U

  -- The context SCT n = (A₀, A₁, ..., Aₙ₋₁) consists of fillers of cells up to
  -- (and including) dimension (n-1).
  SCT O = ◆
  SCT (1+ n) = SCT n ∷ (n -Fillers)

  open is-sieve

  Sk b h (1+ t) iS =
    ̂Σ[ s ∈ Prev-Sk ]
      let
        Aₕ : Tm {SCT (1+ h)} ((h -Fillers) [ π (h -Fillers) ])
        Aₕ = υ (h -Fillers)

        ∂cell : Tm (M h)
        ∂cell = {!!}
      in {!s!}
    where
      Prev-Sk : Ty (SCT (1+ h))
      Prev-Sk = Sk b h t (is-sieve-prev-t iS)

  Sk b O O iS = ̂⊤
  Sk b (1+ h) O iS = Sk b h (Hom-size h b) (is-sieve-bhtmax (S≤→≤ (hcond iS)))
                       [ π ((1+ h)-Fillers) ]

  Sk→ b h (1+ t) iS f s = {!s!}
  Sk→ b O O iS f s = ̂*
  Sk→ b (1+ h) O iS {m} f s = {!s!}
  {-
  With the signature
    (b h t : ℕ) (iS : is-sieve b h t)
    {m : ℕ} (f : Hom m b)
    → Tm (Sk b h t iS)
    → Tm (Sk-unc ([ b , h , t ]∩[ m , f ] iS)),
  the (b , 1+ h , 0) case results in having an argument
    s : Tm (Sk b (1+ h) O iS),
  definitionally
    s : Tm {SCT (2+ h)}
           (Sk b h (Hom-size h b) (is-sieve-bhtmax (S≤→≤ (hcond iS))) [ π ((1+ h)-Fillers) ])
  when the goal is
    ? : Tm (Sk-unc ([ b , 1+ h , O ]∩[ m , f ] iS)),
  which is definitionally
    ? : Tm (Sk-unc ([ b , h , Hom-size h b ]∩[ m , f ] (sieve-conds (S≤→≤ hcond) (inl idp)))).
  -}
