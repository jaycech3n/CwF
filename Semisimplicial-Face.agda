{-# OPTIONS --without-K --termination-depth=2 #-}

module Semisimplicial-Face where

open import Face
open import CwF


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

  open import CwFTools piStr

  SST  : (n : ℕ) → WFCon (S n)
  Sk   : (k n : ℕ) ⦃ k<n : k < n ⦄ → Ty (to-Con (SST k))
  Sk→  : (k : ℕ) (m n : ℕ) ⦃ eₘ : k < m ⦄ ⦃ eₙ : k < n ⦄
         {l : ℕ} → Face n (S m) {l} → Tm (Sk k n) → Tm (Sk k m)
         -- Note that k in `Face n k` is *length* instead of dimension

  SST O = ◆₊ ∷₊ U
  SST (S k) = SST k ∷₊ Sk k (S k) ⦃ ltS ⦄ ̂→ U

  -- This corresponds to the `Π(f : Δ₊(k+1, n)). Y(SK→(f, x))` part of SK in ACK
  -- '16. It adds (k+1)-faces to a k-skeleton of Δⁿ.
  Sk-rec : (k n : ℕ) ⦃ k<n : k < n ⦄ {l : ℕ}
           (f : Face n (S (S k)) {l})
           (x : Tm {to-Con (SST (S k) ∷₊ Sk k n [ p ])} (Sk k n [ p ] [ p ]))
           → Ty (to-Con (SST (S k) ∷₊ Sk k n [ p ]))

  Sk O n = (el (υ (SST O) O ↑)) ˣ (S n)
  Sk (S k) n ⦃ Sk<n ⦄ = ̂Σ[ x ∈ Sk k n ⦃ S<-< Sk<n ⦄ [ p ] ]
    (Sk-rec k n ⦃ S<-< Sk<n ⦄
            (last {n} {S (S k)} n ⦃ inl idp ⦄ ⦃ ≤-ap-S (inr Sk<n) ⦄) x)

  {- Because we don't have Fin in the internal CwF we have to externalize the Π
  type over f : [k] →+ [n] used in the formulation of SK in ACK '16. That is, we
  have a ̂Σ in place of ACK's Π. This is to be constructed by recursion over the
  faces, externally. -}

  private
    instance
      solve-< : ∀ {n} → n < S n
      solve-< = ltS

  {-# TERMINATING #-} -- Recursive call not structurally smaller
  Sk-rec k n (ff .(S (S k))) x =
    el ((
      (tr Tm (
          (Sk k (S k) ̂→ U) [ p ] [ p ]

          =⟨ (ap (_[ p ]) ̂→-[]) ∙ ̂→-[] ⟩

          Sk k (S k) [ p ] [ p ] ̂→ U [ p ] [ p ]

          =⟨ (ap (λ ◻ → ◻ [ p ] [ p ]) U-[]) ∙ (ap (_[ p ]) U-[]) ∙ U-[]
           |in-ctx (̂Π (Sk k (S k) [ p ] [ p ])) ⟩

          (̂Π[ x ∈ Sk k (S k) [ p ] [ p ] ] U)

          =∎)
          (υ (SST (S k) ∷₊ Sk k n [ p ]) 1)
      )
      ` {!-- I don't think this hole is fillable; not with Sk→ being in the outer layer!}
    ) ↑)

  Sk-rec k n (ext i f ⦃ e' ⦄) x = Sk-rec k n prev x ̂× {!!}
    where prev = pred ⦃ <-S≤ (≤-<-< (Face-k≤l f) e') ⦄ (ext i f)
  {-
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
      ` (wkₒ (wkₒ (Sk→ O 1 n ⦃ (O<S O) ⦄ ⦃ O<n ⦄ (ext ⦃ e ⦄ ⦃ e' ⦄ vtx))) x)
    ) ↑)
  -}

  Sk→ = {!!}
