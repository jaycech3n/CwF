{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import CwF

module CwFTools {i} {C : WildCategory {i}} {cwf : WildCwFStructure C}
  (piStr : PiStructure cwf)
  where

open WildCwFStructure cwf
open PiStructure piStr

wk : ∀ {Γ} {A B C : Ty Γ}
     → Tm (A ̂→ B)
     → Tm (A [ p {Γ} {C} ] ̂→ B [ p {Γ} {C} ])
wk f = tr Tm ̂→-[] (f [ p ]ₜ)

-- Is this true?
-- wk' : ∀ {...}1 → (Tm A → Tm B) → Tm (A [ p ]) → Tm (B [ p ])
