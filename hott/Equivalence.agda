{-# OPTIONS --without-K #-}

module hott.Equivalence where

open import hott.Base

private
  variable
    ℓ₁ ℓ₂ ℓ₃ : ULevel

tr-Π-≃-l : {A : Type ℓ₁} {B : Type ℓ₂} (P : B → Type ℓ₃) (e : A ≃ B)
           → ((b : B) → P b) → ((a : A) → P (–> e a))
tr-Π-≃-l P e f = f ∘ –> e

tr-Π-≃-r : {A : Type ℓ₁} {B : Type ℓ₂} (P : A → Type ℓ₃) (e : A ≃ B)
           → ((a : A) → P a) → (b : B) → P (<– e b)
tr-Π-≃-r P e f = f ∘ <– e

tr-Σ-≃-l : {A : Type ℓ₁} {B : Type ℓ₂} (C : B → Type ℓ₃) (e : A ≃ B)
           → Σ[ b ∈ B ] C b → Σ[ a ∈ A ] C (–> e a)
tr-Σ-≃-l C e (b , c) = <– e b , tr C (! (<–-inv-r e b)) c

tr-Σ-≃-r : {A : Type ℓ₁} {B : Type ℓ₂} (C : A → Type ℓ₃) (e : A ≃ B)
           → Σ[ a ∈ A ] C a → Σ[ b ∈ B ] C (<– e b)
tr-Σ-≃-r C e (a , c) = –> e a , tr C (! (<–-inv-l e a)) c
