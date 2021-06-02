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

  -- is there a more principle way of doing this?
  uncurried-Sk : (s : Sieve) → Ty (SST (S (get-h s)))
  uncurried-Sk ((b , h , t) , p) = Sk b h t p


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


  Skm  : (b h t : ℕ) → (p : isSieve (b , h , t)) → (k : ℕ)
         → (f : k →⁺ b) → Tm (Sk b h t p)  → Tm (uncurried-Sk [ b , h , t , p ]∩[ k , f ])

  -- this case copies everything from [_,_,_,_]∩[_,_] and add-component
  Skm b    h (S t) p k f sk = -- we probably need to split into all the cases of `Sk`.
    let
      last-component : S h →⁺ b
      last-component = decode {S h} {b} (t , S≤-< (snd p))
      sieve-without-last : Sieve
      sieve-without-last = [ b , h , t , (fst p , S≤-≤ (snd p)) ]∩[ k , f ]
      add-new? : Dec (last-component ⊆₊ f)
      add-new? = last-component ⊆₊? f
    in
       {!!}
       {- Coprod-rec {A = last-component ⊆₊ f} {B = ¬ (last-component ⊆₊ f)} {C = Sieve}
         (λ  last⊆₊f → add-component sieve-without-last) -- why not just (b , h , S t) , p?
         (λ ¬last⊆₊f → sieve-without-last)
         add-new? -}

  Skm b    O    O  p k f = {!!}

  Skm b (S h)   O  p k f = {!!}


{- replicate:
[ b , h , S t , p ]∩[ k , f ] =
  let
    last-component : S h →⁺ b
    last-component = decode {S h} {b} (t , S≤-< (snd p)) -- Not a mistake: t
                                                         -- instead of (S t) as
                                                         -- arg to `decode`.
    sieve-without-last : Sieve
    sieve-without-last = [ b , h , t , (fst p , S≤-≤ (snd p)) ]∩[ k , f ]
    add-new? : Dec (last-component ⊆₊ f)
    add-new? = last-component ⊆₊? f
  in
     Coprod-rec {A = last-component ⊆₊ f} {B = ¬ (last-component ⊆₊ f)} {C = Sieve}
       (λ  last⊆₊f → add-component sieve-without-last) -- why not just (b , h , S t) , p?
       (λ ¬last⊆₊f → sieve-without-last)
       add-new?
[ _ ,   O , O , _ ]∩[ k , f ] = (k , O , O) , (O≤ k) , (O≤ (binom k 1))
[ b , S h , O , p ]∩[ k , f ] =
  [ b , h , binom b (S h) , (S≤-≤ (fst p) , inl idp) ]∩[ k , f ]
-}




  {- Note: In

  test : ℕ → ℕ → ℕ
  test O O = {!!}
  test (S h) O = {!!}
  test h (S t) = {!!}

  the last line does not hold definitionally. Why?
  If we move it two lines up, the problem disappears.
  Is this a bug?
  -}

  -- Given a term in a "partial skeleton" over the sieve `(b , h , t)`,
  -- we want to project out the components to get a term in the
  -- "partial skeleton" over `(b, b-2, max)`.
  -- There's a 95% risk that I've made some +-1 error here.
  -- ???????

  -- calc-matching : (b h t : ℕ) (p : isSieve (b , h , t)) (S h ≤ b) (sk : Tm (Sk b h t p)) → {!Tm (M₊ !}
  -- calc-matching = {!!}




  SST O = ◆
  SST 1 = ◆ ∷ U -- Assuming a unit type in the CwF structure would avoid this special case. Does it cause problems later?
  SST (S (S n)) = SST (S n) ∷
                      (M₊ n ̂→ U)


  Sk b    O       O   iS = U -- again: this would be the unit type, but we don't have a unit type. The approach here is to plug in a random thing (e.g. U) and never use this case. BETTER: Maybe just introduce a unit type, see above!
  Sk b    O    (S O)  iS = {!el (ν {◆} {U})!} -- need to substitute.
  Sk b    O (S (S t)) iS = {!!}

  -- next case is easy because (b,Sh,O) is the same as (b,h,max)
  Sk b (S h)      O   iS = (Sk b h (binom b (S h)) (≤-trans lteS (fst iS) , inl idp)) [ p ]
  Sk b (S h)    (S t)  iS = {!!}

{- TODO: Should we do it without a unit type or with? With is technically weaker, but without is hackier. -}
