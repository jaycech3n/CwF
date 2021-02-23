{-# OPTIONS --without-K --termination-depth=2 #-}

{--- Semisimplicial types in internal CwFs ---}

module Semisimplicial4 where

open import CwF
open import Sieves

module _ {i} (C : WildCategory {i}) (cwF : WildCwFStructure C)
  (piStr : PiStructure cwF) (sigmaStr : SigmaStructure cwF)
  (uStr : UStructure cwF)
  where
  open WildCwFStructure cwF
  open PiStructure piStr
  open SigmaStructure sigmaStr
  open UStructure uStr

  SST  : ℕ → Con
  SST₋ : ℕ → Con
  fill : (n : ℕ) → Ty (SST₋ n) -- (fill n) is the type of n-dim fillers
  ∂Δ   : (n : ℕ) → Ty (SST n)  -- Beware: (∂Δ n) is the type of labelings of the
                               -- boundary of Δⁿ⁺¹! (i.e. n is the dimension of
                               -- the _boundary_, not the simplex)

  SST n = SST₋ (S n)

  SST₋ O = ◆
  SST₋ (S n) = SST₋ n ∷ fill n

  fill O = U
  fill (S n) = ∂Δ n ̂→ U

  module fillers where
    -- The type of i-fillers, lifted to context SST n
    fill' : (i n : ℕ) ⦃ i≤n : i ≤ n ⦄ → Ty (SST n)
    fill' O O = fill O [ p ]
    fill' O (S n) = fill' O n [ p ]
    fill' (S i) (S n) ⦃ inl _ ⦄ = fill (S n) [ p ] -- i = n
    fill' (S i) (S n) ⦃ inr x ⦄ = fill' (S i) n ⦃ S<S-dec-r x ⦄ [ p ] -- i < n

    -- (∂Δ i), lifted to SST n
    ∂Δ' : (i n : ℕ) ⦃ i≤n : i ≤ n ⦄ → Ty (SST n)
    ∂Δ' O O = ∂Δ O
    ∂Δ' O (S n) = ∂Δ' O n [ p ]
    ∂Δ' (S i) (S n) ⦃ inl _ ⦄ = ∂Δ (S n)
    ∂Δ' (S i) (S n) ⦃ inr x ⦄ = ∂Δ' (S i) n ⦃ S<S-dec-r x ⦄ [ p ]

    -- Coercions through all the projections
    fill'O-is-U : (n : ℕ) → fill' O n == U
    fill'O-is-U O = U-[]
    fill'O-is-U (S n) = (fill'O-is-U n |in-ctx _[ p ]) ∙ U-[]

    -- Strangeness!
    fill'S-is-Pi : (i n : ℕ) ⦃ Si≤n : S i ≤ n ⦄
                 → fill' (S i) n == (∂Δ' i n ⦃ {!≤-dec-l Si≤n!} ⦄ ̂→ U)

    fill'S-is-Pi O (S O) ⦃ Si≤n ⦄
      = fill' (S O) (S O) ⦃ {!Si≤n!} ⦄
      =⟨ ̂→-[] ⟩ ∂Δ O [ p ] ̂→ U [ p ]
      =⟨ U-[] |in-ctx (∂Δ O [ p ] ̂→_) ⟩ ∂Δ O [ p ] ̂→ U =∎

    fill'S-is-Pi O (S (S n))
      = fill' (S O) (S (S n)) ⦃ ≤-ap-S {!O≤ (S n)!} ⦄
      =⟨ idp ⟩ fill' (S O) (S n) ⦃ ≤-ap-S (O≤ n) ⦄ [ p ]
      =⟨ fill'S-is-Pi O (S n) ⦃ {!!} ⦄ |in-ctx _[ p ] ⟩ (∂Δ' O (S n) ̂→ U) [ p ]
      =⟨ {!!} ⟩ _ =∎

    fill'S-is-Pi (S i) (S n) = {!!}
    fill'S-is-Pi O O = {!!}
    fill'S-is-Pi (S i) O = {!!}

    A : (i : ℕ) {n : ℕ} ⦃ i≤n : i ≤ n ⦄ → Tm (fill' i n)
    A O {O} = ν
    A O {S n} = A O {n} [ p ]ₜ
    A (S i) {S n} ⦃ inl _ ⦄ = ν
    A (S i) {S n} ⦃ inr x ⦄ = A (S i) {n} ⦃ S<S-dec-r x ⦄ [ p ]ₜ

  open fillers

  ∂Δ n = {!!} -- sk n (S n)
