{-# OPTIONS --without-K #-}

{--- Semisimplicial types in internal CwFs ---}

module Semisimplicial where

open import CwF
open import Sieves

{- The combinatorics of faces

coords n k
  Gives the i-faces of Δⁿ for 0 ≤ i ≤ k as a list organized in blocks by
  dimension. An i-face is given by a sequence of i+1 points.

face-coords n xs
  xs is a (k+1)-sequence representing a k-face of Δⁿ. face-coords then gives the
  indicators in `coords k n` of the subfaces of xs.
-}

coords : (n k : ℕ) → List (List Seq)
coords n O = Seq+ (S O) O n :: nil
coords n (S k) = snoc (coords n k) (Seq+ (S (S k)) O n)

dim : Seq → ℕ
dim (x ::∎) = O
dim (x :: xs) = S (dim xs)

face-coords : (n : ℕ) → Seq → List (List Bool)
face-coords n xs = map (map (_⊆ xs)) (coords n (dim xs))

test = {!coords 3 1!}
test' = {!face-coords 3 (0 :: 2 :: 3 ::∎)!}

{- Semisimplicial types -}

module _ {i} (C : WildCategory {i}) (cwF : WildCwFStructure C)
  (piStr : PiStructure cwF) (sigmaStr : SigmaStructure cwF)
  (uStr : UStructure cwF)
  where
  open WildCwFStructure cwF
  open PiStructure piStr
  open SigmaStructure sigmaStr
  open UStructure uStr

  {-
  The main definitions are the following (intuitively):
    SST n   ─ The context (A₀ : U, A₁ : A₀ × A₀ → U, ..., Aₙ : ... → U).
    A i n   ─ Aᵢ in context SST n as above.
    X i n   ─ The type of Aᵢ in context SST n.
    sk k n  ─ k-skeleton of Δⁿ.

  In addition, there are a couple of ancilliary definitions.

  SST₋ is an intermediate construct to more conveniently type shape and Sk.
  By definition, SST₋ n = SST (n-1) for n ≥ 1.

  face k n xs ν picks out the subtuple of ν : sk k n [ p ] corresponding to
  the xs-th k-subface and all its subfaces.
  -}
  SST  : ℕ → Con
  SST₋ : ℕ → Con
  X    : (i n : ℕ) ⦃ le : i ≤ n ⦄ → Ty (SST n)
  A    : (i n : ℕ) ⦃ le : i ≤ n ⦄ → Tm (X i n)
  sk   : (k n : ℕ) ⦃ lt : k < n ⦄ ⦃ nz : O < n ⦄ → Ty (SST₋ n)
  face : (n : ℕ) (xs : Seq) ⦃ lt : dim xs < n ⦄ ⦃ nz : O < n ⦄
         → Tm (sk (dim xs) n [ p ]) → {!!}

  SST₋ O = ◆
  SST₋ (S n) = SST n

  SST O = ◆ ∷ U
  SST (S n) = SST n ∷ (sk n (S n) ̂→ U)

  X O O = U [ p ]
  X O (S n) = X O n [ p ]
  X (S i) (S n) ⦃ inl _ ⦄ = (sk n (S n) ̂→ U) [ p ] -- i = n
  X (S i) (S n) ⦃ inr x ⦄ = X (S i) n ⦃ S<S-dec-r x ⦄ [ p ] -- i < n

  A O O = ν
  A O (S n) = A O n [ p ]ₜ
  A (S i) (S n) ⦃ inr x ⦄ = A (S i) n ⦃ S<S-dec-r x ⦄ [ p ]ₜ
  A (S i) (S n) ⦃ inl _ ⦄ = ν

  {-
  In order to define sk we need coercions showing that the Xᵢₙ defined above
  have particular forms.
  -}
  XO=U : (n : ℕ) → X O n == U
  XO=U O     = U-[]
  XO=U (S n) = X O n [ p ]
             =⟨ XO=U n |in-ctx _[ p ] ⟩ U [ p ]
             =⟨ U-[] ⟩ U =∎

  private
    σ : (i n : ℕ) ⦃ le : S i ≤ n ⦄ → Ty (SST n)
    σ i O ⦃ inl () ⦄
    σ i O ⦃ inr () ⦄
    σ i (S n) ⦃ inl _ ⦄ = sk n (S n) [ p ]
    σ i (S n) ⦃ inr x ⦄ = σ i n ⦃ S<S-dec-r x ⦄ [ p ]

    τ : (i n : ℕ) ⦃ le : S i ≤ n ⦄ → Ty (SST n)
    τ i O ⦃ inl () ⦄
    τ i O ⦃ inr () ⦄
    τ i (S n) ⦃ inl _ ⦄ = U [ p ]
    τ i (S n) ⦃ inr x ⦄ = τ i n ⦃ S<S-dec-r x ⦄ [ p ]

    τ=U : ∀ {i n} ⦃ le : S i ≤ n ⦄ → τ i n == U
    τ=U {i} {O} ⦃ inl () ⦄
    τ=U {i} {O} ⦃ inr () ⦄
    τ=U {i} {S n} ⦃ inl _ ⦄ = U-[]
    τ=U {i} {S n} ⦃ inr x ⦄ =
      (τ=U {i} {n} ⦃ S<S-dec-r x ⦄ |in-ctx _[ p ]) ∙ U-[]

  XS=̂→ : (i n : ℕ) ⦃ le : S i ≤ n ⦄ → X (S i) n == (σ i n ̂→ τ i n)
  XS=̂→ i O ⦃ inl () ⦄
  XS=̂→ i O ⦃ inr () ⦄
  XS=̂→ i (S n) ⦃ inl _ ⦄ = ̂→-[]
  XS=̂→ i (S O) ⦃ inr (ltSR ()) ⦄
  XS=̂→ i (S (S .i)) ⦃ inr ltS ⦄ = (̂→-[] |in-ctx _[ p ]) ∙ ̂→-[]
  XS=̂→ i (S (S n)) ⦃ inr (ltSR x) ⦄ =
    (XS=̂→ i n ⦃ S<S-dec-r x ⦄ |in-ctx (λ ◻ → ◻ [ p ] [ p ]))
    ∙ (̂→-[] |in-ctx _[ p ])
    ∙ ̂→-[]

  private
    module coercions where
      instance
        XO-coercion : ∀ {n} → Coerceable (Tm (X O n)) (Tm U)
        coerce ⦃ XO-coercion {n} ⦄ = tr Tm (XO=U n)

      instance
        XS-coercion : ∀ {i n} ⦃ le : S i ≤ n ⦄
                    → Coerceable (Tm (X (S i) n [ p ]))
                                 (Tm (σ i n [ p ] ̂→ τ i n [ p ]))
        coerce ⦃ XS-coercion {i} {n} ⦄ =
          tr Tm ((XS=̂→ i n |in-ctx _[ p ]) ∙ ̂→-[])

  open coercions

  face n (x ::∎) ν = {!!}
  face n (x :: xs) ν = {!!}

  sk O (S n) =
    el (coerce ⦃ XO-coercion {n} ⦄ (A O n)) ˣ S (S n)
  sk (S k) (S n) ⦃ lt ⦄ ⦃ nz ⦄ =
    ̂Σ (sk k (S n) ⦃ <-dec-l lt ⦄ ⦃ nz ⦄)
      (el
        (coerce ⦃ {!!} ⦄
          (coerce ⦃ XS-coercion {k} {n} ⦃ S<S-dec-r lt ⦄ ⦄
                    (A (S k) n ⦃ S<S-dec-r lt ⦄ [ p ]ₜ)
           ` {!!})))
