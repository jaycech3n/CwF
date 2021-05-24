{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import CwF

module CwFTools {i} {C : WildCategory {i}} {cwf : WildCwFStructure C}
  (piStr : PiStructure cwf)
  where

open WildCwFStructure cwf
open PiStructure piStr

-- wk : Tm (A ̂→ B) → Tm (A [ p ] ̂→ B [ p ])

wkₒ : ∀ {Γ} {A B C D : Ty Γ}
     → (f : Tm A → Tm B)
     → Tm (A [ p {Γ} {C} ]) → Tm (B [ p {Γ} {D} ])
wkₒ {Γ} {A} {B} {C} {D} f x =
  {!!}
