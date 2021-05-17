{-# OPTIONS --without-K --termination-depth=2 #-}

module Semisimplicial3 where

open import Face
open import CwF
  hiding ( Fin )


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
  Sk→  : (k : ℕ) {m n : ℕ} ⦃ eₘ : k < m ⦄ ⦃ eₙ : k < n ⦄
         {i : ℕ} → Face n m i → Tm (Sk k n) → Tm (Sk k m)

  SST O = ◆₊ ∷₊ U
  SST (S k) = SST k ∷₊ Sk k (S k) ⦃ ltS ⦄ ̂→ U

  -- This is the `Π(f : Δ₊(k+1, n)). Y(SK→(f, x))` part of SK in ACK '16.
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

  Sk-rec O n ⦃ O<n ⦄ x (ext vtx) = -- Base case; fill the [0,1]-face
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
      ` {!the (0,1)-subtuple of x!}
    ) ↑)

  {- This next hole should be ((Sk-rec f) ̂× (a filler of the subtuple of x
  indexed by (nxt f))). (Recall terminology: given a semisimplicial type (A₀,
  ...), Aₖ is the type of k-fillers, i.e. fillers of k-faces, i.e. a filler of a
  k-face f is an element of Aₖ(f). -}
  Sk-rec O n x {i = S i} (nxt f) =
    {!!}

  {- Here f = [i,] is a single vertex, and we want ((Sk-rec [i,n]) ̂× (a filler
  of the subtuple of x indexed by (ext (nxt f)). -}
  Sk-rec O n x {i = S (S i)} (ext (nxt f)) =
    {!!}

  -- ((Sk-rec f) ̂× (a filler of the subtuple of x indexed by (nxt f)))
  Sk-rec (S k) n x (nxt f) = {!!}

  Sk-rec (S k) n x (ext (nxt f)) = {!!}
  Sk-rec (S k) n x (ext (ext f)) = {!!}

  Sk→ = {!!}
