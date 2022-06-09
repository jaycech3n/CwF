{-# OPTIONS --without-K #-}

{--- Shaped sieves in well presented semicategories ---}

open import SuitableSemicategory

module ShapedSieves ⦃ I : WellPresentedSemicategory ⦄ where
open WellPresentedSemicategory I

open import DSM _≟-ℕ_


{- Sieve shapes -}

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

Shape : Type₀
Shape = Σ[ s ∈ ℕ × ℕ × ℕ ]
          let i = fst s
              h = 2nd s
              t = 3rd s
          in is-sieve i h t

apex : Shape → ℕ
apex ((i , _ , _) , _) = i

height : Shape → ℕ
height ((_ , h , _) , _) = h

width : Shape → ℕ
width ((_ , _ , t) , _) = t

sieve-cond : (((i , h , t) , _) : Shape) → is-sieve i h t
sieve-cond (_ , iS) = iS

Shape= : {s s' : Shape}
         → apex s == apex s'
         → height s == height s'
         → width s == width s'
         → s == s'
Shape= idp idp idp = pair= idp (prop-path is-sieve-is-prop _ _)

-- Basic shapes

empty-sieve : ∀ i → is-sieve i 0 0
hcond (empty-sieve i) = O≤ _
tcond (empty-sieve i) = O≤ _

full-sieve : ∀ i h → h ≤ i → is-sieve i h (Hom-size i h)
hcond (full-sieve i h h≤i) = h≤i
tcond (full-sieve i h h≤i) = lteE

shape-from-next-t : ∀ {i h t} → is-sieve i h (1+ t) → is-sieve i h t
shape-from-next-t iS = sieve-conds (hcond iS) (S≤→≤ (tcond iS))

shape-from-next-h : ∀ {i h} → is-sieve i (1+ h) O → is-sieve i h (Hom-size i h)
shape-from-next-h iS = sieve-conds (≤-trans lteS (hcond iS)) lteE


{- Interpretation of shapes

We define the interpretation of a sieve shape (i, h, t) in terms of decidable
subsets of morphisms of I.
-}

⟦_,_,_⟧ : (i h t : ℕ) → is-sieve i h t → DSM
⟦ i , h , 1+ t ⟧ iS =
  add-arrow (i , h , [t]) (⟦ i , h , t ⟧ (shape-from-next-t iS))
  where [t] = Hom[ i , h ]# (t , <→≤→< ltS (tcond iS))
⟦ i , O , O ⟧ iS = Ø
⟦ i , 1+ h , O ⟧ iS = ⟦ i , h , Hom-size i h ⟧ (shape-from-next-h iS)




{- Shape intersection -}

[_,_,_]∩[_,_] : (i h t : ℕ) (m : ℕ) (f : Hom i m) → is-sieve i h t → Shape

width-of-∩ : (i h t : ℕ) (m : ℕ) (f : Hom i m) (iS : is-sieve i h t)
             → height ([ i , h , t ]∩[ m , f ] iS) == h
             → width ([ i , h , t ]∩[ m , f ] iS) ≤ Hom-size m h

[ i , h , 1+ t ]∩[ m , f ] iS
 with Hom[ i , h ]# (t , S≤→< (tcond iS)) factors-through? f
... | inr no = [ i , h , t ]∩[ m , f ] (shape-from-next-t iS)
... | inl (w , _)
       with height ([ i , h , t ]∩[ m , f ] (shape-from-next-t iS)) <? h
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

              prev-∩ = [ i , h , t ]∩[ m , f ] (shape-from-next-t iS)
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
... | inr no = height-of-∩ i h t m f (shape-from-next-t iS)
... | inl yes
       with height ([ i , h , t ]∩[ m , f ] (shape-from-next-t iS)) <? h
...       | inl <h = lteE
...       | inr ≮h = lteE
height-of-∩ i O O m f iS = lteE
height-of-∩ i (1+ h) O m f iS =
  ≤-trans (height-of-∩ i h (Hom-size i h) m f (shape-from-next-h iS)) lteS


-- The definition of width-of-∩ duplicates the where clauses in the definition
-- of [_,_,_]∩[_,_]. We could merge the two, but then things might get a bit
-- harder to read.

width-of-∩ i h (1+ t) m f iS p
 with Hom[ i , h ]# (t , S≤→< (tcond iS)) factors-through? f
... | inr no = width-of-∩ i h t m f (shape-from-next-t iS) p
... | inl (w , _)
       with height ([ i , h , t ]∩[ m , f ] (shape-from-next-t iS)) <? h
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
              prev-∩ = [ i , h , t ]∩[ m , f ] (shape-from-next-t iS)
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
    height≤h : height ([ i , h , Hom-size i h ]∩[ m , f ] (shape-from-next-h iS)) ≤ h
    height≤h = height-of-∩ i h (Hom-size i h) m f (shape-from-next-h iS)

    contr : 1+ h ≤ h
    contr = tr (_≤ h) p height≤h


apex-of-∩ : (i h t : ℕ) (m : ℕ) (f : Hom i m) (iS : is-sieve i h t)
            → apex ([ i , h , t ]∩[ m , f ] iS) == m
apex-of-∩ i h (1+ t) m f iS
 with Hom[ i , h ]# (t , S≤→< (tcond iS)) factors-through? f
... | inr no = apex-of-∩ i h t m f (shape-from-next-t iS)
... | inl yes
       with height ([ i , h , t ]∩[ m , f ] (shape-from-next-t iS)) <? h
...       | inl <h = idp
...       | inr ≮h = idp
apex-of-∩ i O O m f iS = idp
apex-of-∩ i (1+ h) O m f iS = apex-of-∩ i h (Hom-size i h) m f (shape-from-next-h iS)
