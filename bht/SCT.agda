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

  Sk[_,_,_,_] : (b h t : ℕ) → is-sieve b h t
                → (i : ℕ) → h ≤ i
                → Ty (SCT (1+ i))

  Sk-unc      : (((_ , h , _) , _) : Sieve)
                → (i : ℕ) → h ≤ i
                → Ty (SCT (1+ i))
  Sk-unc ((b , h , t) , iS) i icond = Sk[ b , h , t , iS ] i icond

  Sk→[_,_,_,_]∩[_,_] : (b h t : ℕ) (iS : is-sieve b h t)
                        (m : ℕ) (f : Hom m b)
                        (i : ℕ) (icond : h ≤ i)
                        → Tm (Sk[ b , h , t , iS ] i icond)
                        → Tm (Sk-unc
                               ([ b , h , t ]∩[ m , f ] iS)
                               i (∩-h≤' iS i icond))

  -- The matching object
  M[_]   : (h i : ℕ) → h ≤ i → Ty (SCT i)
  M[ O ] _ _ = ̂⊤
  M[ 1+ h ] O (inl ())
  M[ 1+ h ] (1+ i) icond =
    Sk[ 1+ h , h , Hom-size h (1+ h) , is-sieve-bhtmax lteS ] i (≤-cancel-S icond)

  _-Fillers : ∀ h {i} → {h ≤ i} → Ty (SCT i)
  _-Fillers h {i} {icond} = M[ h ] i icond ̂→ U

  -- The context SCT n = (A₀, A₁, ..., Aₙ₋₁) consists of fillers of cells up to
  -- (and including) dimension (n-1).
  SCT O = ◆
  SCT (1+ n) = SCT n ∷ (n -Fillers) {n} {lteE}

  Sk-unc= : {s@((_ , h , _) , _) s'@((_ , h' , _) , _) : Sieve}
            → s == s'
            → {i : ℕ} {icond : h ≤ i} {icond' : h' ≤ i}
            → Sk-unc s i icond == Sk-unc s' i icond'
  Sk-unc= {s} {.s} idp {i} = ap (Sk-unc s i) (≤-has-all-paths _ _)

  Sk[ b , h , 1+ t , iS ] i icond = {!!}
  Sk[ b , O , O , iS ] i icond = ̂⊤
  Sk[ b , 1+ h , O , iS ] O (inl ())
  Sk[ b , 1+ h , O , iS ] (1+ i) icond =
    Sk[ b , h , Hom-size h b , is-sieve-prev-h iS ] (1+ i) (S≤→≤ icond)

  open is-sieve

  Sk→[ b , h , 1+ t , iS ]∩[ m , f ] i icond s = {!!}
  Sk→[ b , O , O , iS ]∩[ m , f ] i icond s = ̂*
  Sk→[ b , 1+ h , O , iS ]∩[ m , f ] O (inl ())
  Sk→[ b , 1+ h , O , iS ]∩[ m , f ] (1+ i) icond s =
    tr Tm
       (Sk-unc=
         {s  = [ b , h , Hom-size h b ]∩[ m , f ]
                 (sieve-conds (S≤→≤ (hcond iS)) lteE)}
         {s' = [ b , 1+ h , O ]∩[ m , f ] iS }
         idp)
       (Sk→[ b , h , Hom-size h b , is-sieve-prev-h iS ]∩[ m , f ]
           (1+ i) (S≤→≤ icond) s)
