{-# OPTIONS --without-K #-}

open import SuitableSemicategories

{--- Shapes of linear sieves in suitable semicategories ---}

module Shapes ⦃ I : SuitableSemicategory ⦄ where

open SuitableSemicategory I


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


{- Basic shapes -}

degen-shape : ∀ i h → h ≤ i → is-shape i h O
degen-shape i h h≤i = shape-conds h≤i (O≤ _)

empty-shape : ∀ i → is-shape i O O
empty-shape i = degen-shape i O (O≤ _)

full-shape : ∀ i h → h ≤ i → is-shape i h (Hom-size i h)
full-shape i h h≤i = shape-conds h≤i lteE

shape-from-next-t : ∀ {i h t} → is-shape i h (1+ t) → is-shape i h t
shape-from-next-t iS = shape-conds (hcond iS) (S≤→≤ (tcond iS))

shape-from-next-h : ∀ {i h} → is-shape i (1+ h) O → is-shape i h (Hom-size i h)
shape-from-next-h {i} {h} iS = full-shape i h (≤-trans lteS (hcond iS))


{- Shape normalization -}

norm : ∀ i h t → is-shape i h t → Shape
norm i h (1+ t) iS = (i , h , 1+ t) , iS
norm i (1+ h) O iS = (i , h , Hom-size i h) , shape-from-next-h iS
norm i O O iS = (i , O , O) , iS
