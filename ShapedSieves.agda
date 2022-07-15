{-# OPTIONS --without-K #-}

open import SuitableSemicategories

{--- Shaped sieves in well presented semicategories ---}

module ShapedSieves ⦃ I : SuitableSemicategory ⦄ where

open import DSM _≟-ℕ_

open SuitableSemicategory I


{- Sieve shapes

"Shapes" are just triples of numbers satisfying certain conditions.
-}

record is-shape (i h t : ℕ) : Type₀ where
  constructor shape-conds
  field
    hcond : h ≤ i
    tcond : t ≤ Hom-size i h

open is-shape public

is-shape= : ∀ {i h t} {iS iS' : is-shape i h t}
            → hcond iS == hcond iS'
            → tcond iS == tcond iS'
            → iS == iS'
is-shape= idp idp = idp

is-shape-is-prop : ∀ {i h t} → is-prop (is-shape i h t)
is-shape-is-prop = all-paths-is-prop
                   λ{(shape-conds hcond tcond)
                     (shape-conds hcond' tcond')
                   → is-shape= (prop-path ≤-is-prop hcond hcond')
                               (prop-path ≤-is-prop tcond tcond')}

Shape : Type₀
Shape = Σ[ s ∈ ℕ × ℕ × ℕ ]
          let i = fst s
              h = 2nd s
              t = 3rd s
          in is-shape i h t

apex : Shape → ℕ
apex ((i , _ , _) , _) = i

height : Shape → ℕ
height ((_ , h , _) , _) = h

width : Shape → ℕ
width ((_ , _ , t) , _) = t

shape-cond : (((i , h , t) , _) : Shape) → is-shape i h t
shape-cond (_ , iS) = iS

Shape= : {s s' : Shape}
         → apex s == apex s'
         → height s == height s'
         → width s == width s'
         → s == s'
Shape= idp idp idp = pair= idp (prop-path is-shape-is-prop _ _)

-- Basic shapes

empty-shape : ∀ i → is-shape i O O
empty-shape i = shape-conds (O≤ _) (O≤ _)

-- Note Hom-size i h could be 0!
full-shape : ∀ i h → h ≤ i → is-shape i h (Hom-size i h)
full-shape i h h≤i = shape-conds h≤i lteE

shape-from-next-t : ∀ {i h t} → is-shape i h (1+ t) → is-shape i h t
shape-from-next-t iS = shape-conds (hcond iS) (S≤→≤ (tcond iS))

shape-from-next-h : ∀ {i h} → is-shape i (1+ h) O → is-shape i h (Hom-size i h)
shape-from-next-h {i} {h} iS = full-shape i h (≤-trans lteS (hcond iS))


{- Shape intersection -}

factors-cumul : ∀ {i h m} → (t : Fin (Hom-size i h)) → Hom i m → DSHom m h
factors-cumul t f g = to-Bool (idx-of (g ◦ f) ≤?-Fin t)

[_,_,_]∩[_,_] : (i h t : ℕ) (m : ℕ) (f : Hom i m) → is-shape i h t → Shape
[ i , h , 1+ t ]∩[ m , f ] iS
 with Hom[ i , h ]# (t , S≤→< (tcond iS)) factors-through? f
... | inr no = [ i , h , t ]∩[ m , f ] (shape-from-next-t iS)
... | inl (w , _) = (m , h , new-width) ,
                      shape-conds (inr (Hom-inverse m h w)) width-cond
      where
        incr-width : Σ[ t ∈ ℕ ] t ≤ Hom-size m h
        incr-width = size (factors-cumul (t , S≤→< (tcond iS)) f)

        new-width = fst incr-width
        width-cond = snd incr-width
[ i ,   O  , O ]∩[ m , f ] iS = (m , O , O) , empty-shape m
[ i , 1+ h , O ]∩[ m , f ] iS = [ i , h , Hom-size i h ]∩[ m , f ]
                                  (full-shape i h (≤-trans lteS (hcond iS)))

height-of-∩ : (i h t : ℕ) (iS : is-shape i h t) {m : ℕ} (f : Hom i m)
              → height ([ i , h , t ]∩[ m , f ] iS) ≤ h -- normalize this h?
height-of-∩ i h (1+ t) iS f
 with Hom[ i , h ]# (t , S≤→< (tcond iS)) factors-through? f
... | inr no = height-of-∩ i h t (shape-from-next-t iS) f
... | inl yes = lteE
height-of-∩ i O O iS f = lteE
height-of-∩ i (1+ h) O iS f =
  ≤-trans
    (height-of-∩ i h (Hom-size i h) (shape-from-next-h iS) f)
    lteS
