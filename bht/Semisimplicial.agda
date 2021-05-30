{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import CwF
open import bht.Sieves

module bht.Semisimplicial {i} (C : WildCategory {i})
  (cwF : WildCwFStructure C) (piStr : PiStructure cwF)
  (sigmaStr : SigmaStructure cwF) (uStr : UStructure cwF)
  where
  open WildCwFStructure cwF
  open PiStructure piStr
  open SigmaStructure sigmaStr
  open UStructure uStr

  -- SST n is the context (A₀:U, A₁:A₀×A₀→U, A₂:Σ(x y z : A₀).A₁(x,y)×A₁(y,z)×A₁(x,z)→U, ...)
  SST  : ℕ → Con

  -- Sk gives, for every sieve s, the type of "partial boundaries" with shape given by s.
  Sk   : (b h t : ℕ) → isSieve(b , h , t) → Ty (SST (S h))

  {- Matching Object -

  TL;DR: The matching object (at level n) is just the skeleton Sk Sn n Sn.

  In general: If A : I → Type is a Reedy fibrant diagram, the "matching object"
  at "index" i ∈ I is what A(i) may depend on in the type-theoretic formulation;
  i.e. A(i) : M(i) ^→ U in our formulation.
  Here, M O should be the unit type, which we haven't assumed, so we start with
  M 1 instead (which we write as M₊ O).

  TODO: To avoid this ulgy problem (it gets even uglier below), we could just add a unit
  type to the CwF structure!
-}

  M₊ : (n : ℕ) → Ty (SST (S n))
  M₊ n = Sk (S (S n)) n (binom (S (S n)) (S n)) (≤-trans lteS lteS , inl idp)

  SST O = ◆
  SST 1 = ◆ ∷ U -- Assuming a unit type in the CwF structure would avoid this special case. Does it cause problems later?
  SST (S (S n)) = SST (S n) ∷
                      (M₊ n ̂→ U)


  Sk b    O       O   iS = U -- again: this would be the unit type, but we don't have a unit type. The approach here is to plug in a random thing (e.g. U) and never use this case. BETTER: Maybe just introduce a unit type, see above!
  Sk b    O    (S O)  iS = {!el (ν {◆} {U})!} -- need to substitute.
  Sk b    O (S (S t)) iS = {!!}

  -- next case is easy because (b,Sh,O) is the same as (b,h,max)
  Sk b (S h)      O   iS = (Sk b h (binom b (S h)) (≤-trans lteS (fst iS) , inl idp)) [ p ]
  Sk b    h    (S t)  iS = {!!}

{- TODO: Should we do it without a unit type or with? With is technically weaker, but without is hackier. -}
