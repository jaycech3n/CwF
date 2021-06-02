{-# OPTIONS --without-K --termination-depth=2 --allow-unsolved-metas #-}

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

  -- SST n is the context
  --   (A₀: U,
  --    A₁: A₀×A₀ → U,
  --    A₂: Σ(x y z : A₀). A₁(x,y) × A₁(y,z) × A₁(x,z) → U,
  --    ...,
  --    Aₙ₋₁: ... → U)
  SST : ℕ → Con

  -- Sk gives, for every sieve s, the type of "partial boundaries" with shape given by s.
  Sk : (b h t : ℕ) → isSieve(b , h , t) → Ty (SST (S h))

  -- Is there a more principled way of doing this?
  uncurried-Sk : (s : Sieve) → Ty (SST (S (get-h s)))
  uncurried-Sk ((b , h , t) , p) = Sk b h t p


  {- Matching Object -

  TL;DR: The matching object (at level n) is just the skeleton Sk Sn n Sn.

  In general: If A : I → Type is a Reedy fibrant diagram, the "matching object"
  at "index" i ∈ I is what A(i) may depend on in the type-theoretic formulation;
  i.e. A(i) : M(i) ^→ U in our formulation.

  Here, M O should be the unit type, which we haven't assumed, so we start with
  M 1 instead (which we write as M₊ O).

  TODO: To avoid this ugly problem (it gets even uglier below), we could just add a unit
  type to the CwF structure! -}

  -- M₊ n is the matching object at level n+1.
  M₊ : (n : ℕ) → Ty (SST (S n))
  M₊ n = Sk (S (S n)) n (binom (S (S n)) (S n)) (≤-trans lteS lteS , inl idp)

  -- Josh: Don't need this level of generality, really only need the k = h+1 case?
  --Skm : (b h t : ℕ) → (p : isSieve (b , h , t)) → (k : ℕ)
  --      → (f : k →⁺ b) → Tm (Sk b h t p) → Tm (uncurried-Sk [ b , h , t , p ]∩[ k , f ])
  --Skm = {!!}

  -- Given a term in a "partial skeleton" over the sieve (b, h, t), we want to
  -- project out the components to get a term in the partial skeleton over (b,
  -- b-2, max).
  calc-matching : (b h t : ℕ) (p : isSieve (b , S h , t)) (f : S (S h) →⁺ b)
                  → t ≤ fst (encode f)
                  → Tm (Sk b (S h) t p)
                  → Tm (M₊ h)
  calc-matching = {!!}


  SST O = ◆
  SST 1 = ◆ ∷ U -- Assuming a unit type in the CwF structure would avoid this
                -- special case. Does it cause problems later?
  SST (S (S n)) = SST (S n) ∷ (M₊ n ̂→ U)


  Sk b    O       O   iS = U -- Again: this would be the unit type, but we don't
                             -- have a unit type. The approach here is to plug
                             -- in a random thing (e.g. U) and never use this
                             -- case. BETTER: Maybe just introduce a unit type,
                             -- see above!
  Sk b    O    (S O)  iS = el (ν {◆} {U} ↑)
  Sk b    O (S (S t)) iS = Sk b O (S t) (prev-is-sieve iS) ̂× el (ν {◆} {U} ↑)
  -- Next case is easy because (b,Sh,O) is the same as (b,h,max)
  Sk b (S h)      O   iS = (Sk b h (binom b (S h)) (≤-trans lteS (fst iS) , inl idp)) [ p ]
  Sk b (S h)   (S t)  iS = ̂Σ[ x ∈ Sk b (S h) t (prev-is-sieve iS) ] {!use calc-matching; here we run into the previously discussed question of weakening Tm A → Tm B to Tm (A [ p_A ]) → Tm (B [ p_A ]) (here → is outer!)!}
