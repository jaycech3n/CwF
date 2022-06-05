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

sieve-cond : (((i , h , t) , _) : Sieve) → is-sieve i h t
sieve-cond (_ , iS) = iS

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
tcond (full-sieve i h h≤i) = lteE

sieve-from-next-t : ∀ {i h t} → is-sieve i h (1+ t) → is-sieve i h t
sieve-from-next-t iS = sieve-conds (hcond iS) (S≤→≤ (tcond iS))

sieve-from-next-h : ∀ {i h} → is-sieve i (1+ h) O → is-sieve i h (Hom-size i h)
sieve-from-next-h iS = sieve-conds (≤-trans lteS (hcond iS)) lteE


{- Sieve intersection -}

[_,_,_]∩[_,_] : (i h t : ℕ) (m : ℕ) (f : Hom i m) → is-sieve i h t → Sieve

apex-of-∩ : (i h t : ℕ) (m : ℕ) (f : Hom i m) (iS : is-sieve i h t)
            → apex ([ i , h , t ]∩[ m , f ] iS) == m

height-of-∩ : (i h t : ℕ) (m : ℕ) (f : Hom i m) (iS : is-sieve i h t)
              → height ([ i , h , t ]∩[ m , f ] iS) ≤ h

monotone-∩ : (i h t : ℕ) (m : ℕ) (f : Hom i m) (iS : is-sieve i h t)
             → {t' : ℕ} → {1+ t' == t}
             → (s : ℕ)
             → s < width ([ i , h , t ]∩[ m , f ] iS)
             → to-ℕ (idx-of ((Hom[ m , h ]# (s , {!!})) ◦ f)) ≤ t'

[ i , h , 1+ t ]∩[ m , f ] iS
 with Hom[ i , h ]# (t , S≤→< (tcond iS)) factors-through? f
... | inr no = [ i , h , t ]∩[ m , f ] (sieve-from-next-t iS)
... | inl (w , _) =
        if (height prev-∩ <? h)
           (λ <h → (m , h , #-Hom-from-O-val) ,
                     sieve-conds (inr (Hom-inverse h m w)) #-Hom-from-O-cond)
           (λ ≮h → (m , h , {!!}) ,
                     {!!})
      where
        prev-∩ = [ i , h , t ]∩[ m , f ] (sieve-from-next-t iS)

        O-Fin = 0 , Hom[ m , h ]-inhab w
        [O] = Hom[ m , h ]# O-Fin
        [t] = Hom[ i , h ]# (t , S≤→< (tcond iS))

        #-Hom-from-O = #-Hom[ m , h ]-from
                         (λ g → g ◦ f == [t])
                         (λ g → g ◦ f ≟-Hom [t]) [O]

        #-Hom-from-O-val : ℕ
        #-Hom-from-O-val = fst #-Hom-from-O

        #-Hom-from-O-cond : #-Hom-from-O-val ≤ Hom-size m h
        #-Hom-from-O-cond = tr (λ □ → □ + #-Hom-from-O-val ≤ _)
                               (ap fst (idx-of-Hom# O-Fin))
                               (snd #-Hom-from-O)

        [prev-∩-width] = Hom[ m , h ]# (width prev-∩ , {!!})
        {-
        #-Hom-from-prev-width = #-Hom[ m , h ]-from
                                  (λ g → g ◦ f == [t])
                                  (λ g → g ◦ f ≟-Hom [t]) [O]
        -}
[ i ,   O  , O ]∩[ m , f ] iS = (m , 0 , 0) ,
                                  empty-sieve m
[ i , 1+ h , O ]∩[ m , f ] iS = [ i , h , Hom-size i h ]∩[ m , f ]
                                  (full-sieve i h (≤-trans lteS (hcond iS)))

apex-of-∩ i h (1+ t) m f iS
 with Hom[ i , h ]# (t , S≤→< (tcond iS)) factors-through? f
... | inr no = apex-of-∩ i h t m f (sieve-from-next-t iS)
... | inl yes
       with height ([ i , h , t ]∩[ m , f ] (sieve-from-next-t iS)) <? h
...       | inl <h = idp
...       | inr ≮h = idp
apex-of-∩ i O O m f iS = idp
apex-of-∩ i (1+ h) O m f iS = apex-of-∩ i h (Hom-size i h) m f (sieve-from-next-h iS)

height-of-∩ i h (1+ t) m f iS
 with Hom[ i , h ]# (t , S≤→< (tcond iS)) factors-through? f
... | inr no = height-of-∩ i h t m f (sieve-from-next-t iS)
... | inl yes
       with height ([ i , h , t ]∩[ m , f ] (sieve-from-next-t iS)) <? h
...       | inl <h = lteE
...       | inr ≮h = lteE
height-of-∩ i O O m f iS = lteE
height-of-∩ i (1+ h) O m f iS =
  ≤-trans (height-of-∩ i h (Hom-size i h) m f (sieve-from-next-h iS)) lteS

monotone-∩ = {!!}
