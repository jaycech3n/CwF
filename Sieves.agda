{-# OPTIONS --without-K #-}

{--- Shaped sieves in suitable inverse semicategories ---}

open import SuitableSemicategory
open import Arithmetic
open import Fin

module Sieves ⦃ I : SuitableSemicategory ⦄ where

open SuitableSemicategory.SuitableSemicategory I


{- Shaped sieves -}

record is-sieve (i h t : ℕ) : Type₀ where
  constructor sieve-conds
  field
    hcond : h ≤ i
    tcond : t ≤ Hom-size i h

open is-sieve

is-sieve= : ∀ {i h t} {iS iS' : is-sieve i h t}
            → hcond iS == hcond iS'
            → tcond iS == tcond iS'
            → iS == iS'
is-sieve= idp idp = idp

is-sieve-is-prop : ∀ {i h t} → is-prop (is-sieve i h t)
is-sieve-is-prop = all-paths-is-prop
                   λ{(sieve-conds hcond tcond)
                     (sieve-conds hcond' tcond')
                   → is-sieve= (prop-path ≤-is-prop hcond hcond')
                               (prop-path ≤-is-prop tcond tcond')}

Sieve : Type₀
Sieve = Σ[ s ∈ ℕ × ℕ × ℕ ]
          let i = fst s
              h = 2nd s
              t = 3rd s
          in is-sieve i h t

apex : Sieve → ℕ
apex ((i , _ , _) , _) = i

height : Sieve → ℕ
height ((_ , h , _) , _) = h

width : Sieve → ℕ
width ((_ , _ , t) , _) = t

sieve-cond-of : (((i , h , t) , _) : Sieve) → is-sieve i h t
sieve-cond-of (_ , iS) = iS

Sieve= : {s s' : Sieve}
         → apex s == apex s'
         → height s == height s'
         → width s == width s'
         → s == s'
Sieve= idp idp idp = pair= idp (prop-path is-sieve-is-prop _ _)

-- Basic sieves

empty-sieve : ∀ i → is-sieve i 0 0
hcond (empty-sieve i) = O≤ _
tcond (empty-sieve i) = O≤ _

full-sieve : ∀ i h → h ≤ i → is-sieve i h (Hom-size i h)
hcond (full-sieve i h h≤i) = h≤i
tcond (full-sieve i h h≤i) = inl idp

sieve-from-prev-t : ∀ {i h t} → is-sieve i h (1+ t) → is-sieve i h t
sieve-from-prev-t iS = sieve-conds (hcond iS) (S≤→≤ (tcond iS))


{- Sieve intersection -}

[_,_,_]∩[_,_] : (i h t : ℕ) (m : ℕ) (f : Hom i m) → is-sieve i h t → Sieve

-- Need some simultaneously defined properties of ∩

[ i ,   O  , O ]∩[ m , f ] iS = (m , 0 , 0) ,
                                  empty-sieve m
[ i , 1+ h , O ]∩[ m , f ] iS = [ i , h , Hom-size i h ]∩[ m , f ]
                                  (full-sieve i h (≤-trans lteS (hcond iS)))
[ i , h , 1+ t ]∩[ m , f ] iS =
  if in-restriction?
     (λ yes → if (height prev-∩ <? h)
                 (λ <h → (i , h , {!!}) , {!!})
                 (λ ≮h → {!!}))
     (λ no → prev-∩)
  where
    [t] = Hom[ i , h ]# (t , S≤→< (tcond iS))
    in-restriction? = Σ-Hom? (λ g → g ◦ f == [t]) (λ g → g ◦ f ≟-Hom [t])
    prev-∩ = [ i , h , t ]∩[ m , f ] (sieve-from-prev-t iS)
