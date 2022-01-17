{-# OPTIONS --without-K --termination-depth=2 #-}

module bht.SCT-simple-attempt where

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

  Sk[_,_,_,_] : (b h t : ℕ) → is-sieve b h t
                → Ty (SCT (1+ h))

  Sk-unc      : (((_ , h , _) , _) : Sieve)
                → Ty (SCT (1+ h))
  Sk-unc ((b , h , t) , iS) = Sk[ b , h , t , iS ]

  Sk→[_,_,_,_]∩[_,_] : (b h t : ℕ) (iS : is-sieve b h t)
                       (m : ℕ) (f : Hom m b)
                       → Tm (Sk[ b , h , t , iS ])
                       → Tm (Sk-unc ([ b , h , t ]∩[ m , f ] iS))

  -- The matching object
  M[_]   : (h : ℕ) → Ty (SCT h)
  M[ O ] = ̂⊤
  M[ 1+ h ] =
    Sk[ 1+ h , h , Hom-size h (1+ h) , is-sieve-bhtmax lteS ]

  _-Fillers : ∀ h → Ty (SCT h)
  _-Fillers h = M[ h ] ̂→ U

  -- The context SCT n = (A₀, A₁, ..., Aₙ₋₁) consists of fillers of cells up to
  -- (and including) dimension (n-1).
  SCT O = ◆
  SCT (1+ n) = SCT n ∷ (n -Fillers)

  Sk[ b , h , 1+ t , iS ] =
    ̂Σ[ s ∈ Prev-Sk ]
      {!!}
    where
    Prev-Sk : Ty (SCT (1+ h))
    Prev-Sk = Sk[ b , h , t , is-sieve-prev-t iS ]

  Sk[ b , O , O , iS ] = ̂⊤
  Sk[ b , 1+ h , O , iS ] =
    Sk[ b , h , Hom-size h b , is-sieve-prev-h iS ] [ π (1+ h -Fillers) ]

  open is-sieve

  Sk→[ b , h , 1+ t , iS ]∩[ m , f ] s = {!!}
  Sk→[ b , O , O , iS ]∩[ m , f ] s = ̂*
  Sk→[ b , 1+ h , O , iS ]∩[ m , f ] s =
    Sk→[ b , h , Hom-size h b , is-sieve-prev-h iS ]∩[ m , f ] {!s!}
    {-
    This case shows why the generalization over SCT levels in bht.SCT is the
    right thing to do.

    Here, we have argument
      s : Tm (Sk b (1+ h) O iS),
    definitionally
      s : Tm {SCT (2+ h)} (Sk b h (Hom-size h b) _ [ π (1+ h-Fillers) ]).

    On the other hand, the goal is
      ? : Tm (Sk-unc ([ b , 1+ h , O ]∩[ m , f ] iS)),
    which is definitionally
      ? : Tm {SCT (1+ <dimension of intersection>)}
             (Sk-unc ([ b , h , Hom-size h b ]∩[ m , f ] _)).

    We need to apply Sk→ to s, and so would think to lift it to the right
    context. If we want to do this lifting internally we'd have to internalize
    Sk→ to the CwF, which is already inconvenient. Assuming we do this, however,
    Sk→ is then an internal function in
      Tm (Sk[ b , h , t , iS ]) ̂→ Sk-unc ([ b , h , t ]∩[ m , f ] iS),
    whose codomain lives in some SCT h' where h' depends on the intersection.

    ==> Too many moving parts to internalize; might as well do this "decoupling"
    externally.
    -}
