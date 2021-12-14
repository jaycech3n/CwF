{-# OPTIONS --without-K --termination-depth=2 #-}

module bht.SCT-attempt1 where

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
  SCT-of-Sk : (b h t : ℕ) → Con
  Sk  : (b h t : ℕ) → is-sieve b h t → Ty (SCT-of-Sk b h t)
  M   : (b : ℕ) → Ty (SCT b)

  Sk-unc : (((b , h , t) , _) : Sieve) → Ty (SCT-of-Sk b h t)
  Sk-unc ((b , h , t) , iS) = Sk b h t iS

  Sk→ : (b h t : ℕ) (iS : is-sieve b h t)
        {m : ℕ} (f : Hom m b)
        → Tm (Sk b h t iS)
        → Tm (Sk-unc ([ b , h , t ]∩[ m , f ] iS))

  _-Fillers : (b : ℕ) → Ty (SCT b)
  b -Fillers = M b ̂→ U

  -- The context SCT n = (A₀, A₁, ..., Aₙ₋₁) consists of fillers of cells up to
  -- (and including) dimension (n-1).
  SCT O = ◆
  SCT (1+ n) = SCT n ∷ (n -Fillers)

  -- Normalize (b, h+1, 0)-sieves down.
  SCT-of-Sk b h (1+ t) = SCT (1+ h)
  SCT-of-Sk b O O = SCT 1
  SCT-of-Sk b (1+ h) O = SCT (1+ h)

  -- M b is the "matching object" of the diagram induced by (SCT b).
  M O = ̂⊤
  M (1+ b) with Hom-size b (1+ b)
  ... | r = {!!}
  --Sk (1+ b) b (Hom-size b (1+ b)) (is-sieve-bhtmax lteS)

  open is-sieve

  {-
  ⌊Sk⌋ b h (1+ t) iS = Sk b h (1+ t) iS
  ⌊Sk⌋ b O O iS = Sk b O O iS
  ⌊Sk⌋ b (1+ h) O iS = Sk b h (Hom-size h b) (is-sieve-bhtmax (S≤→≤ (hcond iS)))
  -}

  Sk b h (1+ t) iS =
    {!̂Σ[ s ∈ Prev-Sk ]
      let
        Aₕ : Tm {SCT (1+ h)} ((h -Fillers) [ π (h -Fillers) ])
        Aₕ = υ (h -Fillers)

        ∂cell : Tm (M h) -- [ π (h -Fillers) ]?
        ∂cell = {!!}
      in {!s!}
    where
      Prev-Sk : Ty (SCT-of-Sk b h t)
      Prev-Sk = Sk b h t (is-sieve-prev-t iS)!}

  Sk b O O iS = ̂⊤
  Sk b (1+ h) O iS = {!Sk b h (Hom-size h b) (is-sieve-bhtmax (S≤→≤ (hcond iS)))
                       --[ π ((1+ h)-Fillers) ]!}

  Sk→ b h (1+ t) iS f s = {!s!}
  Sk→ b O O iS f s = ̂*
  Sk→ b (1+ h) O iS {m} f s = Sk→ b h (Hom-size h b)
                                  (is-sieve-bhtmax (S≤→≤ (hcond iS)))
                                  f {!s!}
  {- Goal:
  Tm (Sk-unc ([ b , 1+ h , O ]∩[ m , f ] iS))
  ≡
  Tm (Sk-unc ([ b , h , Hom-size h b ]∩[ m , f ]
                (sieve-conds (S≤→≤ (hcond iS)) (inl idp))))
  -}

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
           (Sk b h (Hom-size h b) (is-sieve-bhtmax (S≤→≤ (hcond iS))) [ π ((1+ h)-Fillers) ]).
  On the other hand, the goal is
    ? : Tm (Sk-unc ([ b , 1+ h , O ]∩[ m , f ] iS)),
  which is definitionally
    ? : Tm {SCT (1+ <dimension of intersection>)}
           (Sk-unc ([ b , h , Hom-size h b ]∩[ m , f ] (sieve-conds (S≤→≤ hcond) (inl idp)))),
  and this <dimension of intersection> is ≤ h.
  ==> Should probably normalize the type of the argument s.
  -}
