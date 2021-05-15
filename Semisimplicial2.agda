{-# OPTIONS --without-K --termination-depth=4 #-}

module Semisimplicial2 where

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

{- Because we don't have Fin in the internal CwF we have to externalize the Π
type over f : [k] →+ [n] used in the formulation of SK in ACK '16. That is, we
have a ̂Σ in place of ACK's Π. This is to be constructed by recursion over the
faces, externally. -}

data Face : (n k : ℕ) → Type₀
last-vertex : ∀ {n k} → Face n k → ℕ

data Face where
  face : (i : ℕ) {n : ℕ} → Face n O
  _,_ : ∀ {m k} (f : Face m k)
          (i : ℕ) ⦃ e : last-vertex f < i ⦄
          {n : ℕ} ⦃ e' : i ≤ n ⦄
        → Face n (S k)

last-vertex (face i) = i
last-vertex (f , i) = i

last-face : (n k : ℕ) ⦃ k≤n : k ≤ n ⦄ → Face n k
last-vertex-last-face : (n k : ℕ) ⦃ k≤n : k ≤ n ⦄
                        → last-vertex (last-face n k) == n

last-face n O = face n
last-face O (S k) ⦃ inr () ⦄
last-face (S n) (S k) ⦃ Sk≤Sn ⦄ =
  _,_ (last-face n k ⦃ ≤-cancel-S Sk≤Sn ⦄) (S n)
      ⦃ tr (_< S n) (! (last-vertex-last-face n k ⦃ ≤-cancel-S Sk≤Sn ⦄)) ltS ⦄
      ⦃ lteE ⦄

last-vertex-last-face n O = idp
last-vertex-last-face O (S k) ⦃ inr () ⦄
last-vertex-last-face (S n) (S k) = idp


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
           (f : Face n (S k))
           → Ty (to-Con (SST (S k) ∷₊ Sk k n [ p ]))

  Sk O n = (el (υ (SST O) O ↑)) ˣ (S n)
  Sk (S k) n ⦃ Sk<n ⦄ = ̂Σ[ x ∈ Sk k n ⦃ S<-< Sk<n ⦄ [ p ] ]
    (Sk-rec k n ⦃ S<-< Sk<n ⦄ x (last-face n (S k) ⦃ inr Sk<n ⦄))

  -- Define the iterated ̂Σ by recursion over the face map f : Face n (S k).
  private
    instance
      solve-S≤-≤ : {m n : ℕ} ⦃ h : S m ≤ n ⦄ → m ≤ n
      solve-S≤-≤ {m} {n} ⦃ inl x ⦄ = tr (m ≤_) x lteS
      solve-S≤-≤ ⦃ inr x ⦄ = S<-≤ x

  --{-# TERMINATING #-}
  Sk-rec .O n x (face O , S O) =
    el ((
      (tr Tm (
          ((el (tr Tm U-[] ν) ̂× el (tr Tm U-[] ν)) ̂→ U) [ p ] [ p ]

          =⟨ (ap (_[ p ]) ̂→-[]) ∙ ̂→-[] ⟩

          (el (tr Tm U-[] ν) ̂× el (tr Tm U-[] ν)) [ p ] [ p ] ̂→ U [ p ] [ p ]

          =⟨ (ap (λ ◻ → ◻ [ p ] [ p ]) U-[]) ∙ (ap (_[ p ]) U-[]) ∙ U-[]
           |in-ctx (̂Π ((el (tr Tm U-[] ν) ̂× el (tr Tm U-[] ν)) [ p ] [ p ])) ⟩

          (̂Π[ x ∈ (el (tr Tm U-[] ν) ̂× el (tr Tm U-[] ν)) [ p ] [ p ] ] U)

          =∎)
          (υ (SST O ∷₊ Sk O 1 ⦃ ltS ⦄ ̂→ U ∷₊ Sk O n [ p ]) 1)
      )
      ` {!the (0,1)-subtuple of x!}
    ) ↑)

  Sk-rec .O n x (face O , S (S j)) = Sk-rec O n x (face O , S j) ̂× {!!}
  Sk-rec .O n x (face (S i) , j) = {!!}
  Sk-rec .(S _) n x ((f , i) , j) = {!!}

  --Sk→ = {!!}