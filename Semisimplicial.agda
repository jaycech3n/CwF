{-# OPTIONS --without-K --show-implicit #-}

{--- Semisimplicial types in internal CwFs ---}

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


  {-- Formalizing semisemiplicial types internally --

  We represent a semisimplicial type by a context of fillers: SST n is the
  context (A₀ : U, A₁ : Aₒ × A₀ → U, ..., Aₙ : ... → U). The formalization is
  better with an additional SST₋ (where SST₋ n = SST (n-1)) to conveniently
  refer to constructions that live in an earlier iteration of SST. We also use
  sk, the codimension-1 skeleton of Δⁿ (more on this below).
  -}

  SST  : ℕ → Con
  SST₋ : ℕ → Con
  sk   : (n : ℕ) → ⦃ O < n ⦄ → Ty (SST₋ n) -- (n-1)-skeleton of Δⁿ

  SST₋ O = ◆
  SST₋ (S n) = SST n

  SST O = ◆ ∷ U
  SST (S n) = SST n ∷ (sk (S n) ̂→ U)


  {- Lifted fillers -}

  -- (fill i {n}) is the type of i-fillers, lifted to context SST n.
  -- Concretely,
  --   fill   O   {n} = U [ p ] ... [ p ] (weakened n times)
  --   fill (S i) {n} = (sk (S n) ̂→ U) [ p ] ... [ p ] (weakened n-i-1 times)
  fill : ∀ (i : ℕ) {n} (i≤n : i ≤ n) → Ty (SST n)
  fill   O   {O}   _ = U [ p ]
  fill (S i) {O}   (inl ())
  fill (S i) {O}   (inr ())
  fill   O   {S n} _ = fill O {n} (O≤ n) [ p ] -- CHOICE
  fill (S i) {S n} (inl Si=Sn) = (sk (S n) ̂→ U) [ p ]
  fill (S i) {S n} (inr Si<Sn) = fill (S i) {n} (decr-<S Si<Sn) [ p ] -- CHOICE

  -- i-fillers, in context SST n
  A : ∀ (i : ℕ) {n} (i≤n : i ≤ n) → Tm (fill i i≤n)
  A   O   {O}   _ = ν
  A (S i) {O}   (inl ())
  A (S i) {O}   (inr ())
  A   O   {S n} _ = A O {n} (O≤ n) [ p ]ₜ -- CHOICE
  A (S i) {S n} (inl Si=Sn) = ν
  A (S i) {S n} (inr Si<Sn) = A (S i) {n} (decr-<S Si<Sn) [ p ]ₜ -- CHOICE

  -- To actually use the fillers (as U and functions to be applied) they have to
  -- be transported along equalities fillO=U and fillS=Pi, defined in the
  -- following module.
  module fillers where
    fillO=U : ∀ n {O≤n : O ≤ n} → fill O O≤n == U :> (Ty (SST n))
    fillO=U O     = U-[]
    fillO=U (S n) = fill O {n} (O≤ n) [ p ] -- CHOICE
                    =⟨ fillO=U n {O≤ n} |in-ctx _[ p ] ⟩ U [ p ] -- CHOICE
                    =⟨ U-[] ⟩ U =∎

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

    -- Coercions
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


  {- Geometry of Δⁿ -}

  data face : (k n : ℕ) → Set
  head : ∀ {k n} → face k n → ℕ

  infix  61 _:∎[_]
  infixr 60 _::_
  data face where
    _:∎[_]  : (i n : ℕ) → ⦃ i≤n : i ≤ n ⦄ → face O n
    _::_    : ∀ {k n} (i : ℕ) (f : face k n) ⦃ i≤head : i ≤ head f ⦄
            → face (S k) n

  head (i :∎[ _ ]) = i
  head (i :: x) = i


  {- Skeleton of Δⁿ and shape of the (b,h,t)-sieve

  The major difficulty is in formulating the definition of sk as an internal
  Σ-type. We use the approach outlined in Sieves.agda to define shapes indexed
  by special sieves of the form "(b,h,t)", but for compatibility with the
  definition of sk and SST we use a slightly different convention from the one
  used there:

  (b,h,t) now means
    [0] ... [h-1] [h] ⇛ [b]
  where all arrows [i] → [b] for 0 ≤ i < h are present, and there are t arrows
  [h] → [b].

  We require t ≥ 1, which also means that the sieve with zero arrows on the
  "top" level [h] → [b] has unique representation (b, h-1, binom (b+1) h).
  -}

  shape : (b h t : ℕ) ⦃ h≤b : h ≤ b ⦄ ⦃ O<b : O < b ⦄ ⦃ O<t : O < t ⦄
          → Ty (SST h)

  -- Attempt: simultaneously define the intersection of an element of shape
  -- (b,h,t) with the f-th h-face of Δᵇ.
  inter : (b h t : ℕ) ⦃ h≤b : h ≤ b ⦄ ⦃ O<b : O < b ⦄ ⦃ O<t : O < t ⦄
          (σ : Tm (shape b h t))
          {i : ℕ} ⦃ i≤h : i ≤ h ⦄
          (f : face (S i) b)
        → Tm (shape (S i) i (S (S i) ch (S i))
                    ⦃ lteS ⦄
                    ⦃ O<S i ⦄
                    ⦃ ch>O (S (S i)) (S i) lteS ⦄)
  inter = {!!}

  -- CHOICES below
  shape (S b) O (S O) =
    el (coerce ⦃ fillO-coercion {O} {O≤ O} ⦄ (A O (O≤ O)))

  shape (S b) O (S (S t)) =
    shape (S b) O (S t) ⦃ O≤ (S b) ⦄ ⦃ O<S b ⦄ ̂×
    el (coerce ⦃ fillO-coercion {O} {O≤ O} ⦄ (A O (O≤ O)))

  shape (S b) (S h) (S O) ⦃ Sh≤Sb ⦄ =
    ̂Σ (shape (S b) h (S (S b) ch S h)
             ⦃ inr (decr-S≤ Sh≤Sb) ⦄
             ⦃ O<S b ⦄
             ⦃ ch>O (S (S b)) (S h) (lteSR Sh≤Sb) ⦄ [ p ])
      (coerce ⦃ {!!} ⦄ (
        coerce ⦃ fillS-coercion {h} {S (S h)} ⦃ lteS ⦄ ⦄ (A (S h) {S (S h)} lteS)
          ` ({!inter (S b) h (S (S b) ch S h)
                   ⦃ {!!} ⦄
                   ⦃ {!!} ⦄
                   ⦃ {!!} ⦄
                   {!ν!} ⦃ {!!} ⦄
                   ({!f!} :> face (S h) (S b))!} [ p ]ₜ [ p ]ₜ)))

  shape (S b) (S h) (S (S t)) = {!!}

  sk (S n) = shape (S n) n (S (S n) ch S n)
                   ⦃ lteS {n} ⦄ ⦃ O<S n ⦄ ⦃ ch>O (S (S n)) (S n) (lteS {S n}) ⦄
