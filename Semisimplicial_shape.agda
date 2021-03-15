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
  sk    : (n : ℕ) → ⦃ O < n ⦄ → Ty (SST₋ n) -- sk n is the (n-1)-skeleton of Δⁿ

  {- Shape of the (b,h,t)-sieve

  For compatibility with the definition of sk and SST we use a slightly
  different convention from the one in Sieves.agda:
  (b,h,t) now means
    [0] ... [h-1] [h] ⇛ [b]
  where all arrows [i] → [b] for 0 ≤ i < h are present, and there are t arrows
  [h] → [b].
  We require t ≥ 1, which also means that the sieve with zero arrows on the
  "top" level has unique representation as (b, h-1, binom (b+1) h).
  -}
  shape : (b h t : ℕ) ⦃ h≤b : h ≤ b ⦄ ⦃ O<b : O < b ⦄ ⦃ O<t : O < t ⦄
          → Ty (SST h)

  SST₋ O = ◆
  SST₋ (S n) = SST n

  SST O = ◆ ∷ U
  SST (S n) = SST n ∷ (sk (S n) ̂→ U)

  module fillers where
    -- (fill i {n}) is the type of i-fillers, lifted to context SST n
    fill : ∀ (i : ℕ) {n} (i≤n : i ≤ n) → Ty (SST n)
    fill   O   {O}   _ = U [ p ]
    fill (S i) {O}   (inl ())
    fill (S i) {O}   (inr ())
    fill   O   {S n} _ = fill O {n} (O≤ n) [ p ] -- CHOICE
    fill (S i) {S n} (inl Si=Sn) = (sk (S n) ̂→ U) [ p ] -- i = n
    fill (S i) {S n} (inr Si<Sn) = fill (S i) {n} (decr-<S Si<Sn) [ p ]
                                   -- i < n -- CHOICE

    -- i-fillers, in context SST n
    A : ∀ (i : ℕ) {n} (i≤n : i ≤ n) → Tm (fill i i≤n)
    A   O   {O}   _ = ν
    A (S i) {O}   (inl ())
    A (S i) {O}   (inr ())
    A   O   {S n} _ = A O {n} (O≤ n) [ p ]ₜ -- CHOICE
    A (S i) {S n} (inl Si=Sn) = ν
    A (S i) {S n} (inr Si<Sn) = A (S i) {n} (decr-<S Si<Sn) [ p ]ₜ -- CHOICE

    fillO=U : ∀ n {O≤n : O ≤ n} → fill O O≤n == U :> (Ty (SST n))
    fillO=U O     = U-[]
    fillO=U (S n) = fill O {n} (O≤ n) [ p ] -- CHOICE
                    =⟨ fillO=U n {O≤ n} |in-ctx _[ p ] ⟩ U [ p ] -- CHOICE
                    =⟨ U-[] ⟩ U =∎

    private
      σ : (i n : ℕ) (Si≤n : S i ≤ n) → Ty (SST n)
      σ i O (inl ())
      σ i O (inr () )
      σ i (S n) (inl _) = sk (S n) [ p ]
      σ i (S n) (inr Si<Sn) = σ i n (decr-<S Si<Sn) [ p ] -- CHOICE

      τ : (i n : ℕ) (Si≤n : S i ≤ n) → Ty (SST n)
      τ i O (inl ())
      τ i O (inr ())
      τ i (S n) (inl _) = U [ p ]
      τ i (S n) (inr Si<Sn) = τ i n (decr-<S Si<Sn) [ p ] -- CHOICE

      τ=U : ∀ {i n} (Si≤n : S i ≤ n) → τ i n Si≤n == U
      τ=U {i} {O} (inl ())
      τ=U {i} {O} (inr ())
      τ=U {i} {S n} (inl _) = U-[]
      τ=U {i} {S n} (inr x) =
        (τ=U {i} {n} (decr-<S x) |in-ctx _[ p ]) ∙ U-[] -- CHOICE

      fillS=Pi' : (i n : ℕ) (Si≤n : S i ≤ n)
                → fill (S i) Si≤n == (σ i n Si≤n ̂→ τ i n Si≤n) :> Ty (SST n)
      fillS=Pi' i O (inl ())
      fillS=Pi' i O (inr ())
      fillS=Pi' i (S n) (inl _) = ̂→-[]
      fillS=Pi' i (S O) (inr (ltSR ()))
      fillS=Pi' i (S (S .i)) (inr ltS) = (̂→-[] |in-ctx _[ p ]) ∙ ̂→-[]
      fillS=Pi' i (S (S n)) (inr (ltSR x)) =
        (fillS=Pi' i n (decr-<S x) |in-ctx (λ ◻ → ◻ [ p ] [ p ])) -- CHOICE
        ∙ (̂→-[] |in-ctx _[ p ])
        ∙ ̂→-[]

    fillS=Pi : (i n : ℕ) (Si≤n : S i ≤ n)
             → fill (S i) Si≤n == (σ i n Si≤n ̂→ U) :> Ty (SST n)
    fillS=Pi i n Si≤n = fillS=Pi' i n Si≤n ∙ (τ=U Si≤n |in-ctx (σ i n Si≤n ̂→_))

    instance
      fillO-coercion : ∀ {n} {O≤n : O ≤ n}
                     → Coerceable (Tm (fill O O≤n)) (Tm U)
      coerce ⦃ fillO-coercion {n} {O≤n} ⦄ = tr Tm (fillO=U n {O≤n})

    instance
      fillS-coercion : ∀ {i n} ⦃ Si≤n : S i ≤ n ⦄
                     → Coerceable (Tm (fill (S i) Si≤n))
                                  (Tm (σ i n Si≤n ̂→ U))
      coerce ⦃ fillS-coercion {i} {n} ⦃ Si≤n ⦄ ⦄ = tr Tm (fillS=Pi i n Si≤n)

  open fillers

  sk (S n) = shape (S n) n (S (S n) ch S n)
                   ⦃ lteS ⦄ ⦃ O<S n ⦄
                   ⦃ O<SSn-ch-Sn ⦄
             where
               O<SSn-ch-Sn : O < S (S n) ch S n
               O<SSn-ch-Sn = tr (O <_) (! (Sn-ch-n (S n))) (O<S (S n))
               -- CHOICES

  -- CHOICES below
  shape (S b) O (S O) =
    el (coerce ⦃ U-coercion ⦄ (A O (O≤ O)))
  shape (S b) O (S (S t)) =
    shape (S b) O (S t) ⦃ O≤ (S b) ⦄ ⦃ O<S b ⦄ ̂×
    el (coerce ⦃ U-coercion ⦄ (A O (O≤ O)))
  shape (S b) (S h) (S O) ⦃ Sh≤Sb ⦄ =
    ̂Σ (shape (S b) h (S (S b) ch (S h))
             ⦃ inr (decr-S≤ Sh≤Sb) ⦄
             ⦃ O<S b ⦄
             ⦃ ch>O (S (S b)) (S h) (lteSR Sh≤Sb) ⦄ [ p ])
      {!!}
  shape (S b) (S h) (S (S t)) = {!!}
