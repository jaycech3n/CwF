{-# OPTIONS --without-K #-}

module hott.Base where

open import HoTT
  renaming
  ( lsucc          to lsuc
  ; transport      to tr
  ; transp-∙       to tr-∙
  ; to-transp      to to-tr
  ; from-transp    to from-tr
  ; ℕ-has-dec-eq   to _≟-ℕ_
  ; Fin-has-dec-eq to _≟-Fin_
  ; <-dec          to _<?_
  ; ≤-dec          to _≤?_
  ; [_]            to ∣_∣ )
  public

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : ULevel


{- Notation -}

pattern 1+ n = S n
pattern 2+ n = S (S n)

Σ-syntax = Σ
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

-- Conditionals

case : {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
       → A ⊔ B → (A → C) → (B → C) → C
case a⊔b a b = ⊔-rec a b a⊔b

if : {A : Type ℓ₁} {B : Type ℓ₂} → Dec A → (A → B) → (¬ A → B) → B
if = case

-- Propositional truncation

∥_∥ : Type ℓ → Type ℓ
∥ A ∥ = Trunc -1 A


{- Inspect -}

-- The inspect idiom, copied from the Agda standard library

record Reveal_·_is_ {A : Type ℓ₁} {B : A → Type ℓ₂}
  (f : (x : A) → B x) (x : A) (y : B x) : Type (lmax ℓ₁ ℓ₂)
  where
  constructor ▹
  field eq : f x == y

inspect : ∀ {A : Type ℓ₁} {B : A → Type ℓ₂}
          (f : (x : A) → B x) (x : A) → Reveal f · x is f x
inspect f x = ▹ idp


{- Triples -}

module _ {A : Type ℓ₁} {B : A → Type ℓ₂} {C : {a : A} (b : B a) → Type ℓ₃} where
  2nd : (u : Σ[ a ∈ A ] Σ[ b ∈ B a ] C b) → B (fst u)
  2nd = fst ∘ snd

  3rd : (u : Σ[ a ∈ A ] Σ[ b ∈ B a ] C b) → C (2nd u)
  3rd = snd ∘ snd


{- Coproducts -}

inl= : {A : Type ℓ₁} {B : Type ℓ₂} {a a' : A} → a == a' → inl a == inl a' :> A ⊔ B
inl= idp = idp

inr= : {A : Type ℓ₁} {B : Type ℓ₂} {b b' : B} → b == b' → inr b == inr b' :> A ⊔ B
inr= idp = idp


{- Maybe -}

-- Could make this dependent, but don't need it.

Maybe : Type ℓ → Type ℓ
Maybe A = A ⊔ ⊤

some : {A : Type ℓ} → A → Maybe A
some a = inl a

none : {A : Type ℓ} → Maybe A
none = inr tt

Maybe-elim : {A : Type ℓ₁} {B : Type ℓ₂}
             → Maybe A → B → (A → B) → B
Maybe-elim m b f = ⊔-elim f (λ _ → b) m

default : {A : Type ℓ₁} {B : Type ℓ₂} → B → (A → B) → Maybe A → B
default _ f (inl a) = f a
default b f (inr _) = b

some≠none : {A : Type ℓ} {a : A} → some a ≠ none
some≠none {a = a} = inl≠inr a tt


{- Decidable types -}

to-Bool : {A : Type ℓ} → Dec A → Bool
to-Bool (inl _) = true
to-Bool (inr _) = false

is-true : Bool → Type₀
is-true true = ⊤
is-true false = ⊥
