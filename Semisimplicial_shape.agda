{-# OPTIONS --without-K #-}

module Semisimplicial_shape where -- (Sieve formulation of skeleton)

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

  SST   : ℕ → Con
  SST₋  : ℕ → Con
  sk    : (n : ℕ) → ⦃ O < n ⦄ → Ty (SST₋ n)

  {- Shape of the (b,h,t)-sieve

  For compatibility with the definition of sk and SST we use a slightly
  different convention from the one in Sieves.agda:
  (b,h,t) now means
    [0] ... [h-1] [h] ⇛ [b]
  where all arrows [i] → [b] for 0 ≤ i < h are present, and there are t arrows
  [h] → [b].
  We require t ≥ 1, which also means that the sieve with zero arrows on the
  "top" level has unique representation as (b, h-1, binom h (b+1)).
  -}
  shape : (b h t : ℕ) ⦃ h≤b : h ≤ b ⦄ ⦃ O<b : O < b ⦄ → Ty (SST₋ b)
          -- (probably also need restriction on t)

  SST₋ O = ◆
  SST₋ (S n) = SST n

  SST O = ◆ ∷ U
  SST (S n) = SST n ∷ (sk (S n) ̂→ U)

  module fillers where
    -- (fill {n} i) is the universe of the type of i-fillers, lifted to context
    -- SST n
    fill : ∀ {n} (i : ℕ) (i≤n : i ≤ n) → Ty (SST n)
    fill {O} O _ = U [ p ]
    fill {O} (S i) (inl ())
    fill {O} (S i) (inr ())
    fill {S n} O _ = fill {n} O (O≤ n) [ p ] -- CHOICE
    fill {S n} (S i) (inl Si=Sn) = (sk (S n) ̂→ U) [ p ] -- i = n
    fill {S n} (S i) (inr Si<Sn) = fill {n} (S i) (dec-<S Si<Sn) [ p ] -- i < n -- CHOICE

    -- i-fillers, in context SST n
    A : ∀ {n} (i : ℕ) (i≤n : i ≤ n) → Tm (fill i i≤n)
    A {O} O _ = ν
    A {O} (S i) (inl ())
    A {O} (S i) (inr ())
    A {S n} O _ = A {n} O (O≤ n) [ p ]ₜ -- CHOICE
    A {S n} (S i) (inl Si=Sn) = ν
    A {S n} (S i) (inr Si<Sn) = A {n} (S i) (dec-<S Si<Sn) [ p ]ₜ -- CHOICE

    fillO=U : ∀ n {O≤n : O ≤ n} → fill {n} O O≤n == U
    fillO=U O     = U-[]
    fillO=U (S n) = fill {n} O (O≤ n) [ p ] -- CHOICE
                       =⟨ fillO=U n {O≤ n} |in-ctx _[ p ] ⟩ U [ p ] -- CHOICE
                       =⟨ U-[] ⟩ U =∎

    private
      σ : (i n : ℕ) (Si≤n : S i ≤ n) → Ty (SST n)
      σ i O (inl ())
      σ i O (inr () )
      σ i (S n) (inl _) = sk (S n) [ p ]
      σ i (S n) (inr Si<Sn) = σ i n (dec-<S Si<Sn) [ p ] -- CHOICE

      τ : (i n : ℕ) (Si≤n : S i ≤ n) → Ty (SST n)
      τ i O (inl ())
      τ i O (inr ())
      τ i (S n) (inl _) = U [ p ]
      τ i (S n) (inr Si<Sn) = τ i n (dec-<S Si<Sn) [ p ] -- CHOICE

      τ=U : ∀ {i n} (Si≤n : S i ≤ n) → τ i n Si≤n == U
      τ=U {i} {O} (inl ())
      τ=U {i} {O} (inr ())
      τ=U {i} {S n} (inl _) = U-[]
      τ=U {i} {S n} (inr x) =
        (τ=U {i} {n} (dec-<S x) |in-ctx _[ p ]) ∙ U-[] -- CHOICE

    fillS=Pi' : (i n : ℕ) (Si≤n : S i ≤ n)
              → fill {n} (S i) Si≤n == (σ i n Si≤n ̂→ τ i n Si≤n)
    fillS=Pi' i O (inl ())
    fillS=Pi' i O (inr ())
    fillS=Pi' i (S n) (inl _) = ̂→-[]
    fillS=Pi' i (S O) (inr (ltSR ()))
    fillS=Pi' i (S (S .i)) (inr ltS) = (̂→-[] |in-ctx _[ p ]) ∙ ̂→-[]
    fillS=Pi' i (S (S n)) (inr (ltSR x)) =
      (fillS=Pi' i n (dec-<S x) |in-ctx (λ ◻ → ◻ [ p ] [ p ])) -- CHOICE
      ∙ (̂→-[] |in-ctx _[ p ])
      ∙ ̂→-[]

    fillS=Pi : (i n : ℕ) (Si≤n : S i ≤ n) → fill {n} (S i) Si≤n == (σ i n Si≤n ̂→ U)
    fillS=Pi i n Si≤n = fillS=Pi' i n Si≤n ∙ (τ=U Si≤n |in-ctx (σ i n Si≤n ̂→_))

    instance
      fillO-coercion : ∀ {n} {O≤n : O ≤ n} → Coerceable (Tm (fill {n} O O≤n)) (Tm U)
      coerce ⦃ fillO-coercion {n} {O≤n} ⦄ = tr Tm (fillO=U n {O≤n})

    instance
      fillS-coercion : ∀ {i n} ⦃ Si≤n : S i ≤ n ⦄
                     → Coerceable (Tm (fill {n} (S i) Si≤n [ p ]))
                                  (Tm (σ i n Si≤n [ p ] ̂→ τ i n Si≤n [ p ]))
      coerce ⦃ fillS-coercion {i} {n} ⦃ Si≤n ⦄ ⦄ =
        tr Tm ((fillS=Pi' i n Si≤n |in-ctx _[ p ]) ∙ ̂→-[])

  open fillers

  sk (S n) = shape (S n) (S n) O ⦃ lteE ⦄ ⦃ O<S n ⦄ -- CHOICES

  shape b O t = {!!}
  shape b (S h) t = {!!}
