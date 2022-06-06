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

width-of-∩ : (i h t : ℕ) (m : ℕ) (f : Hom i m) (iS : is-sieve i h t)
             → height ([ i , h , t ]∩[ m , f ] iS) == h
             → width ([ i , h , t ]∩[ m , f ] iS) ≤ Hom-size m h

monotone-∩ : (i h t : ℕ) (m : ℕ) (f : Hom i m) (iS : is-sieve i h t)
             → {t' : ℕ} → {1+ t' == t}
             → (p : height ([ i , h , t ]∩[ m , f ] iS) == h)
             → (s : ℕ) (lt : s < width ([ i , h , t ]∩[ m , f ] iS))
             → let slt : s < Hom-size m h
                   slt = <→≤→< lt (width-of-∩ i h t m f iS p) in
               to-ℕ (idx-of ((Hom[ m , h ]# (s , slt)) ◦ f)) ≤ t'

[ i , h , 1+ t ]∩[ m , f ] iS
 with Hom[ i , h ]# (t , S≤→< (tcond iS)) factors-through? f
... | inr no = [ i , h , t ]∩[ m , f ] (sieve-from-next-t iS)
... | inl (w , _)
       with height ([ i , h , t ]∩[ m , f ] (sieve-from-next-t iS)) <? h
...       | inl prev-height<h =
              (m , h , #-Hom-from-O-val) ,
                sieve-conds (inr (Hom-inverse h m w)) #-Hom-from-O-cond
            where
              -- If the height of the previous intersection (i, h, t)∩(m, f) is
              -- less than h, then we know (by monotonicity; but we don't need
              -- to prove this here) that [0] ∘ f = [t], so we start counting
              -- from there.

              O-Fin = 0 , Hom[ m , h ]-inhab w
              [O] = Hom[ m , h ]# O-Fin
              [t] = Hom[ i , h ]# (t , S≤→< (tcond iS))

              #-Hom-from-O = #-Hom[ m , h ]-from
                               (λ g → g ◦ f == [t])
                               (λ g → g ◦ f ≟-Hom [t])
                               [O]

              #-Hom-from-O-val = fst #-Hom-from-O

              #-Hom-from-O-cond : #-Hom-from-O-val ≤ Hom-size m h
              #-Hom-from-O-cond = tr (λ □ → □ + #-Hom-from-O-val ≤ _)
                                     (ap fst (idx-of-Hom# O-Fin))
                                     (snd #-Hom-from-O)

...       | inr prev-height≮h =
              (m , h , prev-width + #-Hom-from-prev-val) ,
                sieve-conds (inr (Hom-inverse h m w)) #-Hom-from-prev-cond
            where
              -- If prev-width := height((i, h, t)∩(m, f)) ≮ h (and so in fact
              -- equals h) then we start counting from prev-width. Here we need
              -- to prove that prev-width < |Hom m h| strictly.

              prev-∩ = [ i , h , t ]∩[ m , f ] (sieve-from-next-t iS)
              prev-width = width prev-∩

              prev-width-cond : prev-width < Hom-size m h
              prev-width-cond = {!!}

              [prev-width] = Hom[ m , h ]# (prev-width , prev-width-cond)
              [t] = Hom[ i , h ]# (t , S≤→< (tcond iS))

              #-Hom-from-prev = #-Hom[ m , h ]-from
                                  (λ g → g ◦ f == [t])
                                  (λ g → g ◦ f ≟-Hom [t])
                                  [prev-width]

              #-Hom-from-prev-val = fst #-Hom-from-prev

              #-Hom-from-prev-cond : prev-width + #-Hom-from-prev-val ≤ Hom-size m h
              #-Hom-from-prev-cond =
                tr (λ □ → □ + #-Hom-from-prev-val ≤ _)
                   (ap to-ℕ (idx-of-Hom# (prev-width , prev-width-cond)))
                   (snd #-Hom-from-prev)

[ i ,   O  , O ]∩[ m , f ] iS = (m , 0 , 0) ,
                                  empty-sieve m
[ i , 1+ h , O ]∩[ m , f ] iS = [ i , h , Hom-size i h ]∩[ m , f ]
                                  (full-sieve i h (≤-trans lteS (hcond iS)))


height-of-∩ : (i h t : ℕ) (m : ℕ) (f : Hom i m) (iS : is-sieve i h t)
              → height ([ i , h , t ]∩[ m , f ] iS) ≤ h
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


-- The definition of width-of-∩ duplicates the where clauses in the definition
-- of [_,_,_]∩[_,_]. We could merge the two, but then things might get a bit
-- harder to read.

width-of-∩ i h (1+ t) m f iS p
 with Hom[ i , h ]# (t , S≤→< (tcond iS)) factors-through? f
... | inr no = width-of-∩ i h t m f (sieve-from-next-t iS) p
... | inl (w , _)
       with height ([ i , h , t ]∩[ m , f ] (sieve-from-next-t iS)) <? h
...       | inl prev-height<h = #-Hom-from-O-cond
            where
              O-Fin = 0 , Hom[ m , h ]-inhab w
              [O] = Hom[ m , h ]# O-Fin
              [t] = Hom[ i , h ]# (t , S≤→< (tcond iS))

              #-Hom-from-O = #-Hom[ m , h ]-from
                               (λ g → g ◦ f == [t])
                               (λ g → g ◦ f ≟-Hom [t])
                               [O]

              #-Hom-from-O-val = fst #-Hom-from-O

              #-Hom-from-O-cond : #-Hom-from-O-val ≤ Hom-size m h
              #-Hom-from-O-cond = tr (λ □ → □ + #-Hom-from-O-val ≤ _)
                                     (ap fst (idx-of-Hom# O-Fin))
                                     (snd #-Hom-from-O)
...       | inr prev-height≮h = #-Hom-from-prev-cond
            where
              prev-∩ = [ i , h , t ]∩[ m , f ] (sieve-from-next-t iS)
              prev-width = width prev-∩

              prev-width-cond : prev-width < Hom-size m h
              prev-width-cond = {!!}

              [prev-width] = Hom[ m , h ]# (prev-width , prev-width-cond)
              [t] = Hom[ i , h ]# (t , S≤→< (tcond iS))

              #-Hom-from-prev = #-Hom[ m , h ]-from
                                  (λ g → g ◦ f == [t])
                                  (λ g → g ◦ f ≟-Hom [t])
                                  [prev-width]

              #-Hom-from-prev-val = fst #-Hom-from-prev

              #-Hom-from-prev-cond : prev-width + #-Hom-from-prev-val ≤ Hom-size m h
              #-Hom-from-prev-cond =
                tr (λ □ → □ + #-Hom-from-prev-val ≤ _)
                   (ap to-ℕ (idx-of-Hom# (prev-width , prev-width-cond)))
                   (snd #-Hom-from-prev)

width-of-∩ i O O m f iS p = O≤ _
width-of-∩ i (1+ h) O m f iS p = ⊥-elim (S≰ contr)
  where
    height≤h : height ([ i , h , Hom-size i h ]∩[ m , f ] (sieve-from-next-h iS)) ≤ h
    height≤h = height-of-∩ i h (Hom-size i h) m f (sieve-from-next-h iS)

    contr : 1+ h ≤ h
    contr = tr (_≤ h) p height≤h


apex-of-∩ : (i h t : ℕ) (m : ℕ) (f : Hom i m) (iS : is-sieve i h t)
            → apex ([ i , h , t ]∩[ m , f ] iS) == m
apex-of-∩ i h (1+ t) m f iS
 with Hom[ i , h ]# (t , S≤→< (tcond iS)) factors-through? f
... | inr no = apex-of-∩ i h t m f (sieve-from-next-t iS)
... | inl yes
       with height ([ i , h , t ]∩[ m , f ] (sieve-from-next-t iS)) <? h
...       | inl <h = idp
...       | inr ≮h = idp
apex-of-∩ i O O m f iS = idp
apex-of-∩ i (1+ h) O m f iS = apex-of-∩ i h (Hom-size i h) m f (sieve-from-next-h iS)

monotone-∩ = {!!}
