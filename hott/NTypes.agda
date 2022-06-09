{-# OPTIONS --without-K #-}

module hott.NTypes where

open import hott.Base

private
  variable ℓ ℓ₁ ℓ₂ : ULevel


{- Props -}

prop-equiv : {A : Type ℓ₁} {B : Type ℓ₂}
             ⦃ propA : is-prop A ⦄ ⦃ propB : is-prop B ⦄
             → (A → B) → (B → A) → A ≃ B
prop-equiv ⦃ propA ⦄ ⦃ propB ⦄ f g =
  equiv f g (λ _ → prop-path propB _ _) (λ _ → prop-path propA _ _)


{- Sets -}

is-set-UIP : {A : Type ℓ} {a : A} → is-set A → (p : a == a) → p == idp
is-set-UIP {a = a} s p = prop-path (has-level-apply s a a) p idp

abstract
  is-set-K : {A : Type ℓ₁} {a : A} {C : a == a → Type ℓ₂}
             → is-set A → C idp
             → (p : a == a) → C p
  is-set-K {a = a} s c p rewrite prop-path (has-level-apply s a a) p idp = c
