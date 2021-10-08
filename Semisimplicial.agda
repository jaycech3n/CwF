{-# OPTIONS --without-K --termination-depth=2 #-}

module Semisimplicial where

open import CwF public
open import Sieves

module _ {i} (C : WildCategory {i})
  (cwf : WildCwFStructure C)
  (pistruct : PiStructure cwf)
  (sigmastruct : SigmaStructure cwf)
  (ustruct : UStructure cwf)
  where
  open WildCwFStructure cwf
  open PiStructure pistruct
  open SigmaStructure sigmastruct
  open UStructure ustruct

  SST : ℕ → Con
  Sk  : (n k t : ℕ) → is-sieve n k t → Ty (SST k)

  -- Uncurried Maybe form of Sk
  Sk-aux : (s : Maybe Sieve) → Ty (SST (default O get-k s))
  Sk-aux (inl ((n , k , t) , iS)) = Sk n k t iS
  Sk-aux none = Sk O O 1 (first-is-sieve _ _ lteE)
                -- Slight hack: if the intersection is empty get Sk→ to return
                -- the first vertex of the skeleton.

  Sk→ : (n k t : ℕ) (iS : is-sieve n k t) {m : ℕ} (f : m →+ n)
        → Tm (Sk n k t iS) → Tm (Sk-aux ([ n , k , t ]∩[ m , f ] iS ))

  -- (shape+ n) is the shape of the type of (n+1)-fillers
  shape+ : (n : ℕ) → Ty (SST n)
  shape+ n = (Sk (1+ n) n (binom (2+ n) (1+ n)) (last-is-sieve _ _ lteS)) ̂→ U

  SST O = ◆ ∷ U
  SST (1+ n) = SST n ∷ shape+ n

  -- The only sieve on 0 is (0,0,1)
  Sk O O (1+ t) _ = el (υ U ↓)
  Sk O (1+ k) t (sieve-conds (inl ()) _)

  Sk (1+ n) O (1+ O) _  = el (υ U ↓)
  Sk (1+ n) O (2+ t) iS = Sk (1+ n) O (1+ t) (prev-is-sieve-t iS) ̂× el (υ U ↓)

  Sk (1+ n) (1+ k) (1+ O) iS@(sieve-conds Sk<Sn _) =
    -- "Σ (Sk (1+ n) k (binom (2+ n) (1+ k))) λ s → A₍ₖ₊₁₎ (Sk→ f s)"
    ̂Σ[ s ∈ prev-Sk ] el (tr Tm U↑↑[[]]==U (tr Tm shape↑==̂→ A ` (∂face s ↑ₜ)) ↑ₜ ↓)
    where
      -- Shape of the full k-skeleton of Δ⁽ⁿ⁺¹⁾
      prev-Sk : Ty (SST k ∷ shape+ k)
      prev-Sk = Sk (1+ n) k (binom (2+ n) (1+ k)) (prev-is-sieve-k iS) ↑

      A : Tm ((shape+ k ↑) :> Ty (SST (1+ k)))
      A = υ (shape+ k)

      shape↑==̂→ : (shape+ k ↑) :> Ty (SST k ∷ shape+ k)
                  == (Sk (1+ k) k (binom (2+ k) (1+ k)) _ ↑) ̂→ (U ↑)
      shape↑==̂→ = ̂→-[]

      -- Ugly, but we have to convince Agda that this is still a
      -- universe in the extended context.
      U↑↑[[]]==U : ∀ {t} → U [ π (shape+ k) ]
                             [ π (Sk (1+ k) k (binom (2+ k) (1+ k)) _ ↑) ]
                             [[ t ]]
                           == U
      U↑↑[[]]==U {t} = ap (_[[ t ]] ∘ _[ π _ ]) U-[]
                     ∙ ap _[[ t ]] U-[]
                     ∙ U-[]

      ∂face : (s : Tm (prev-Sk ↑)) → Tm (Sk (1+ k) k (binom (2+ k) (1+ k))
                                        (last-is-sieve (1+ k) k lteS))
      ∂face s = {!Sk→ (1+ n) k (binom (2+ n) (1+ k)) (prev-is-sieve-k iS)
                      (map-of-index (1+ n) (1+ k) 1 iS) ?!}

  Sk (1+ n) (1+ k) (2+ t) (sieve-conds Sk<Sn 2+≤binom) = {!!}

  Sk→ n k t iS f x = {!!}
