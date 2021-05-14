{-# OPTIONS --without-K #-}

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

  -- Define the iterated ̂Σ by recursion over the face map f : Face n (S k).
  Sk-rec : (k n : ℕ) ⦃ k<n : k < n ⦄
           (x : Tm {to-Con (SST (S k) ∷₊ Sk k n [ p ])} (Sk k n [ p ] [ p ]))
           (f : Face n (S k))
           → Ty (to-Con (SST (S k) ∷₊ Sk k n [ p ]))
  Sk-rec .0 n x (face i , j) = {!!}
  Sk-rec .(S _) n x ((f , i) , j) = {!!}

  Sk O n = (el (υ (SST O) O ↑)) ˣ (S n)
  Sk (S k) n ⦃ Sk<n ⦄ = ̂Σ[ x ∈ Sk k n ⦃ S<-< Sk<n ⦄ [ p ] ]
    (Sk-rec k n ⦃ S<-< Sk<n ⦄ x (last-face n (S k) ⦃ inr Sk<n ⦄))

  --Sk→ = {!!}
