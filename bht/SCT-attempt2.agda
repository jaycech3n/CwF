{-# OPTIONS --without-K --termination-depth=2 #-}

module bht.SCT-attempt2 where

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

  SCT             : ℕ → Con
  SCT-of-_-Filler : ℕ → Con
  SCT-of-Sk       : (b h t : ℕ) → Con

  _-Fillers : (h : ℕ) → Ty (SCT-of- h -Filler)

  Sk : (b h t : ℕ) → is-sieve b h t → Ty (SCT-of-Sk b h t)

  Sk-unc : (((b , h , t) , _) : Sieve) → Ty (SCT-of-Sk b h t)
  Sk-unc ((b , h , t) , iS) = Sk b h t iS

  Sk→ : (b h t : ℕ) (iS : is-sieve b h t)
        {m : ℕ} (f : Hom m b)
        → Tm (Sk b h t iS)
        → Tm (Sk-unc ([ b , h , t ]∩[ m , f ] iS))

  -- The context SCT n = (A₀, A₁, ..., Aₙ₋₁) consists of fillers of cells up to
  -- (and including) dimension (n-1).
  SCT O = ◆
  SCT (1+ n) = SCT-of- n -Filler ∷ (n -Fillers)

  SCT-of- O -Filler = SCT O
  SCT-of-(1+ h)-Filler = SCT-of-Sk (1+ h) h (Hom-size h (1+ h))

  SCT-of-Sk b h (1+ t) = SCT (1+ h)
  SCT-of-Sk b O O = SCT O
  SCT-of-Sk b (1+ h) O = SCT-of-Sk b h (Hom-size h b)

  O -Fillers = ̂⊤ ̂→ U
  (1+ h)-Fillers = Sk (1+ h) h (Hom-size h (1+ h)) (is-sieve-bhtmax lteS) ̂→ U

  open is-sieve

  Sk b h (1+ t) iS =
    ̂Σ[ s ∈ Prev-Sk ]
      let
        Aₕ : Tm {SCT (1+ h)} ((h -Fillers) [ π (h -Fillers) ])
        Aₕ = υ (h -Fillers)

        --∂cell : Tm {!!}
        --∂cell = {!!}
      in {!s!}
    where
      Prev-Sk : Ty (SCT (1+ h))
      Prev-Sk = {!Sk b h t (is-sieve-prev-t iS)!} -- Analyze on paper: what's the relation between SCT-of-Sk and SCT-of-_-Filler?

  Sk b O O iS = ̂⊤
  Sk b (1+ h) O iS = Sk b h (Hom-size h b) (is-sieve-prev-h iS)

  Sk→ b h (1+ t) iS f s = {!s!}
  Sk→ b O O iS f s = ̂*
  Sk→ b (1+ h) O iS {m} f s = Sk→ b h (Hom-size h b) (is-sieve-prev-h iS) f s
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
