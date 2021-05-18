{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import CwF

module CwFTools {i} {C : WildCategory {i}} {cwf : WildCwFStructure C}
  (piStr : PiStructure cwf)
  where

open WildCwFStructure cwf
open PiStructure piStr

wk : ∀ {Γ} {A B C D : Ty Γ}
     → (f : Tm A → Tm B)
     → Tm (A [ p {Γ} {C} ]) → Tm (B [ p {Γ} {D} ])
wk {Γ} {A} {B} f x = {!̂λ!}
