{-# OPTIONS --without-K --termination-depth=2 #-}

module Semisimplicial3 where

open import Face
open import CwF
  hiding ( Fin )

-- Keeping Fin around, just in case
data Fin : ℕ → Type₀ where
  fz : {n : ℕ} → Fin (S n)
  fs : {n : ℕ} → Fin n → Fin (S n)

_<Fin_ : {n : ℕ} → Fin n → Fin n → Type₀
i <Fin fz = ⊥
fz <Fin fs _ = ⊤
fs i <Fin fs j = i <Fin j

is-increasing : {m n : ℕ} → (Fin m → Fin n) → Type₀
is-increasing {m} f = {i j : Fin m} → i <Fin j → f i <Fin f j

_→+_ : ℕ → ℕ → Type₀
m →+ n = Σ (Fin m → Fin n) is-increasing


{- Semisimplicial types -}

module _ {i} (C : WildCategory {i}) (cwf : WildCwFStructure C)
  (piStr    : PiStructure cwf)
  (sigmaStr : SigmaStructure cwf)
  (uStr     : UStructure cwf)
  where
  open WildCwFStructure cwf
  open PiStructure piStr
  open SigmaStructure sigmaStr
  open UStructure uStr

  SST  : (n : ℕ) → WFCon (S n)
  Sk   : (k n : ℕ) ⦃ k<n : k < n ⦄ → Ty (to-Con (SST k))
  --Sk→  : (k : ℕ) {m n : ℕ} → m →+ n → Tm (Sk k n) → Tm (Sk k m)

  SST O = ◆₊ ∷₊ U
  SST (S k) = SST k ∷₊ Sk k (S k) ⦃ ltS ⦄ ̂→ U

  Sk-rec : (k n : ℕ) ⦃ k<n : k < n ⦄
           (x : Tm {to-Con (SST (S k) ∷₊ Sk k n [ p ])} (Sk k n [ p ] [ p ]))
           {i : ℕ} (f : Face n (S k) i)
           → Ty (to-Con (SST (S k) ∷₊ Sk k n [ p ]))

  Sk O n = (el (υ (SST O) O ↑)) ˣ (S n)
  Sk (S k) n ⦃ Sk<n ⦄ = ̂Σ[ x ∈ Sk k n ⦃ S<-< Sk<n ⦄ [ p ] ]
    (Sk-rec k n ⦃ S<-< Sk<n ⦄ x (last-face n (S k) ⦃ inr Sk<n ⦄))

  private
    instance
      solve-S≤-≤ : {m n : ℕ} ⦃ h : S m ≤ n ⦄ → m ≤ n
      solve-S≤-≤ {m} {n} ⦃ inl x ⦄ = tr (m ≤_) x lteS
      solve-S≤-≤ ⦃ inr x ⦄ = S<-≤ x

  {- Because we don't have Fin in the internal CwF we have to externalize the Π
  type over f : [k] →+ [n] used in the formulation of SK in ACK '16. That is, we
  have a ̂Σ in place of ACK's Π. This is to be constructed by recursion over the
  faces, externally. -}

  Sk-rec .O n ⦃ O<n ⦄ x (ext (vtx i)) =
    el ((
      (tr Tm (
          ((el (tr Tm U-[] ν) ̂× el (tr Tm U-[] ν)) ̂→ U) [ p ] [ p ]

          =⟨ (ap (_[ p ]) ̂→-[]) ∙ ̂→-[] ⟩

          (el (tr Tm U-[] ν) ̂× el (tr Tm U-[] ν)) [ p ] [ p ] ̂→ U [ p ] [ p ]

          =⟨ (ap (λ ◻ → ◻ [ p ] [ p ]) U-[]) ∙ (ap (_[ p ]) U-[]) ∙ U-[]
           |in-ctx (̂Π ((el (tr Tm U-[] ν) ̂× el (tr Tm U-[] ν)) [ p ] [ p ])) ⟩

          (̂Π[ x ∈ (el (tr Tm U-[] ν) ̂× el (tr Tm U-[] ν)) [ p ] [ p ] ] U)

          =∎)
          (υ (SST O ∷₊ Sk O 1 ⦃ ltS ⦄ ̂→ U ∷₊ Sk O n ⦃ O<n ⦄ [ p ]) 1)
      )
      ` {!the (i, i+1)-subtuple of x!}
    ) ↑)
  Sk-rec .(S _) n x (ext (ext f)) = {!!}
  Sk-rec k n x (ext (nxt f)) = {!!}
  Sk-rec k n x (nxt f) = {!!}

  --Sk→ = {!!}
