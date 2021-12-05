{-# OPTIONS --without-K #-}

module Equivalence where

open import Prelude

tr-Π-≃-l : ∀ {i j k} {A : Type i} {B : Type j} (P : B → Type k) (e : A ≃ B)
        → ((b : B) → P b) → ((a : A) → P (–> e a))
tr-Π-≃-l P e f = f ∘ –> e

tr-Π-≃-r : ∀ {i j k} {A : Type i} {B : Type j} (P : A → Type k) (e : A ≃ B)
         → ((a : A) → P a) → (b : B) → P (<– e b)
tr-Π-≃-r P e f = f ∘ <– e

tr-Σ-≃-l : ∀ {i j k} {A : Type i} {B : Type j} (C : B → Type k) (e : A ≃ B)
           → Σ[ b ∈ B ] C b → Σ[ a ∈ A ] C (–> e a)
tr-Σ-≃-l C e (b , c) = <– e b , tr C (! (<–-inv-r e b)) c

tr-Σ-≃-r : ∀ {i j k} {A : Type i} {B : Type j} (C : A → Type k) (e : A ≃ B)
           → Σ[ a ∈ A ] C a → Σ[ b ∈ B ] C (<– e b)
tr-Σ-≃-r C e (a , c) = –> e a , tr C (! (<–-inv-l e a)) c
