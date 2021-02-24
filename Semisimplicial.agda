{-# OPTIONS --without-K #-}

module Semisimplicial where

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
  sk   : (k n : ℕ) ⦃ k<n : k < n ⦄ ⦃ O<n : O < n ⦄ → Ty (SST₋ n) -- k-skeleton of Δⁿ

  SST₋ O = ◆
  SST₋ (S n) = SST n

  SST O = ◆ ∷ U
  SST (S n) = SST n ∷ (sk n (S n) ̂→ U)

  module fillers where
    -- (fill {n} i) is the universe of the type of i-fillers, lifted to context
    -- SST n
    fill : ∀ {n} (i : ℕ) ⦃ i≤n : i ≤ n ⦄ → Ty (SST n)
    fill {O} O = U [ p ]
    fill {O} (S i) ⦃ inl () ⦄
    fill {O} (S i) ⦃ inr () ⦄
    fill {S n} O = fill {n} O [ p ]
    fill {S n} (S i) ⦃ inl Si=Sn ⦄ = (sk n (S n) ̂→ U) [ p ] -- i = n
    fill {S n} (S i) ⦃ inr Si<Sn ⦄ = fill {n} (S i) ⦃ dec-<S Si<Sn ⦄ [ p ] -- i < n

    -- i-fillers, in context SST n
    A : ∀ {n} (i : ℕ) ⦃ i≤n : i ≤ n ⦄ → Tm (fill i)
    A {O} O = ν
    A {O} (S i) ⦃ inl () ⦄
    A {O} (S i) ⦃ inr () ⦄
    A {S n} O = A {n} O [ p ]ₜ
    A {S n} (S i) ⦃ inl Si=Sn ⦄ = ν
    A {S n} (S i) ⦃ inr Si<Sn ⦄ = A {n} (S i) ⦃ dec-<S Si<Sn ⦄ [ p ]ₜ

    fillO=U : ∀ n → fill {n} O == U
    fillO=U O     = U-[]
    fillO=U (S n) = fill {n} O [ p ]
                  =⟨ fillO=U n |in-ctx _[ p ] ⟩ U [ p ]
                  =⟨ U-[] ⟩ U =∎

    private
      σ : (i n : ℕ) ⦃ Si≤n : S i ≤ n ⦄ → Ty (SST n)
      σ i O ⦃ inl () ⦄
      σ i O ⦃ inr () ⦄
      σ i (S n) ⦃ inl _ ⦄ = sk n (S n) [ p ]
      σ i (S n) ⦃ inr Si<Sn ⦄ = σ i n ⦃ dec-<S Si<Sn ⦄ [ p ]

      τ : (i n : ℕ) ⦃ Si≤n : S i ≤ n ⦄ → Ty (SST n)
      τ i O ⦃ inl () ⦄
      τ i O ⦃ inr () ⦄
      τ i (S n) ⦃ inl _ ⦄ = U [ p ]
      τ i (S n) ⦃ inr Si<Sn ⦄ = τ i n ⦃ dec-<S Si<Sn ⦄ [ p ]

      τ=U : ∀ {i n} ⦃ le : S i ≤ n ⦄ → τ i n == U
      τ=U {i} {O} ⦃ inl () ⦄
      τ=U {i} {O} ⦃ inr () ⦄
      τ=U {i} {S n} ⦃ inl _ ⦄ = U-[]
      τ=U {i} {S n} ⦃ inr x ⦄ =
        (τ=U {i} {n} ⦃ dec-<S x ⦄ |in-ctx _[ p ]) ∙ U-[]

    fillS=Pi' : (i n : ℕ) ⦃ le : S i ≤ n ⦄ → fill (S i) == (σ i n ̂→ τ i n)
    fillS=Pi' i O ⦃ inl () ⦄
    fillS=Pi' i O ⦃ inr () ⦄
    fillS=Pi' i (S n) ⦃ inl _ ⦄ = ̂→-[]
    fillS=Pi' i (S O) ⦃ inr (ltSR ()) ⦄
    fillS=Pi' i (S (S .i)) ⦃ inr ltS ⦄ = (̂→-[] |in-ctx _[ p ]) ∙ ̂→-[]
    fillS=Pi' i (S (S n)) ⦃ inr (ltSR x) ⦄ =
      (fillS=Pi' i n ⦃ dec-<S x ⦄ |in-ctx (λ ◻ → ◻ [ p ] [ p ]))
      ∙ (̂→-[] |in-ctx _[ p ])
      ∙ ̂→-[]

    fillS=Pi : (i n : ℕ) ⦃ le : S i ≤ n ⦄ → fill (S i) == (σ i n ̂→ U)
    fillS=Pi i n ⦃ le ⦄ = fillS=Pi' i n ∙ ({!!} |in-ctx (_ ̂→_))

    instance
      XO-coercion : ∀ {n} → Coerceable (Tm (fill {n} O)) (Tm U)
      coerce ⦃ XO-coercion {n} ⦄ = tr Tm (fillO=U n)

    instance
      XS-coercion : ∀ {i n} ⦃ le : S i ≤ n ⦄
                  → Coerceable (Tm (fill (S i) [ p ]))
                               (Tm (σ i n [ p ] ̂→ τ i n [ p ]))
      coerce ⦃ XS-coercion {i} {n} ⦄ =
        tr Tm ((fillS=Pi' i n |in-ctx _[ p ]) ∙ ̂→-[])

  open fillers


  sk O (S n) =
    el (coerce ⦃ XO-coercion {n} ⦄ (A {n} O)) ˣ S (S n)
  sk (S k) (S n) ⦃ lt ⦄ ⦃ nz ⦄ =
    ̂Σ (sk k (S n) ⦃ dec-S< lt ⦄ ⦃ nz ⦄)
      (el
        (coerce ⦃ {!!} ⦄
          (coerce ⦃ XS-coercion {k} {n} ⦃ dec-<S lt ⦄ ⦄
                    (A {n} (S k) ⦃ dec-<S lt ⦄ [ p ]ₜ)
           ` {!!})))
