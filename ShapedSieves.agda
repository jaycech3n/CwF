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

full-shape' : ∀ i → is-shape i i O
full-shape' i = shape-conds lteE (O≤ _)

shape-from-next-t : ∀ {i h t} → is-shape i h (1+ t) → is-shape i h t
shape-from-next-t iS = shape-conds (hcond iS) (S≤→≤ (tcond iS))

shape-from-next-h : ∀ {i h} → is-shape i (1+ h) O → is-shape i h (Hom-size i h)
shape-from-next-h {i} {h} iS = full-shape i h (≤-trans lteS (hcond iS))

-- Need this lemma for shape normalization. "nd" is for non-degenerate; a
-- degenerate shape is one of the form (i, 1+ h, 0).
nd-shape-height : ∀ i h t → is-shape i h (1+ t) → h < i
nd-shape-height i .i t (shape-conds (inl idp) tcond)
  rewrite endo-Hom-empty i = ⊥-rec (S≰O t tcond)
nd-shape-height i h t (shape-conds (inr u) _) = u


{- Shape normalization -}

norm↓ : ∀ i h t → is-shape i h t → Shape
norm↓ i h (1+ t) iS = (i , h , 1+ t) , iS
norm↓ i (1+ h) O iS = norm↓ i h (Hom-size i h) (shape-from-next-h iS)
norm↓ i O O iS = (i , O , O) , iS

norm↑ : ∀ i h t → is-shape i h t → Shape
norm↑ i .i _ (shape-conds (inl idp) _) = (i , i , O) , full-shape' i
norm↑ i h t (shape-conds (inr h<i) (inl t=max)) =
  (i , 1+ h , O) , (shape-conds (<→S≤ h<i) (O≤ _))
  -- In this case we *don't* want to pattern match on t=max, otherwise the proof
  -- of norm↑-full below does not go through!
norm↑ i h t iS@(shape-conds (inr h<i) (inr t<max)) = (i , h , t) , iS

norm↑-nonfull : ∀ i h t iS → t < Hom-size i h → h == height (norm↑ i h t iS)
norm↑-nonfull i .i t (shape-conds (inl idp) _) _ = idp
norm↑-nonfull i h .(Hom-size i h) (shape-conds (inr _) (inl idp)) u = ⊥-rec (¬-< u)
norm↑-nonfull i h t (shape-conds (inr _) (inr _)) _ = idp

norm↑-full : ∀ i h iS → h < i → 1+ h == height (norm↑ i h (Hom-size i h) iS)
norm↑-full i .i (shape-conds (inl idp) _) u = ⊥-rec (¬-< u)
norm↑-full i h (shape-conds (inr _) (inl p)) _ = idp
norm↑-full i h (shape-conds (inr _) (inr q)) _ = ⊥-rec (¬-< q)

norm∙ : ∀ i h t → is-shape i h t → Shape
norm∙ i h O iS = (i , h , O) , iS
norm∙ i h (1+ t) iS = {!!}


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
[ i , 1+ h , O ]∩[ m , f ] iS = [ i , h , Hom-size i h ]∩[ m , f ]
                                  (full-shape i h (≤-trans lteS (hcond iS)))
[ i ,   O  , O ]∩[ m , f ] iS = (m , O , O) , empty-shape m

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

{- Some normalization issues to deal with in the following definition.......

   In a bit more detail: the definition of [_,_,_]∩[_,_] always gives the
   *minimum* (lexicographic) shape representative of its isomorphism class, so
   that the equality
     [ i , h , t ]∩[ m , f ] iS == (m , m ∸ 1 , Hom-size m (m ∸ 1))    (*)
   is only true up to the equivalence relation. For example, what happens if
     Hom-size m (m ∸ 1)
   is zero? So it seems like we need to normalize the RHS of (*).

   But also, the constraint that m be "small enough" relative to the
   (i,h,t)-sieve references h which is representative-dependent, and causes
   problems with the recursion.
-}

[_,_,_]∩[_↓,_]-eq :
  (i h t m : ℕ) (f : Hom i m) (iS : is-shape i h t)
  → ⦃ m ≤ height (norm↓ i h t iS) ⦄
  → [ i , h , t ]∩[ m , f ] iS
    == norm↓ m m O (full-shape' m)

[_,_,_]∩[_↑,_]-eq :
  (i h t m : ℕ) (f : Hom i m) (iS : is-shape i h t)
  → ⦃ m ≤ height (norm↑ i h t iS) ⦄
  → [ i , h , t ]∩[ m , f ] iS
    == norm↓ m m O (full-shape' m)

[_,_,_]∩[_,_]-eq :
  (i h t m : ℕ) (f : Hom i m) (iS : is-shape i h t)
  → ⦃ m ≤ h ⦄
  → [ i , h , t ]∩[ m , f ] iS
    == norm↓ m m O (full-shape' m)

[ i , h , 1+ t ]∩[ m ↓, f ]-eq iS
  with Hom[ i , h ]# (t , S≤→< (tcond iS)) factors-through? f
[ i , h , 1+ t ]∩[ m ↓, f ]-eq iS ⦃ u ⦄
  | inr no = [ i , h , t ]∩[ m , f ]-eq (shape-from-next-t iS) ⦃ u ⦄
[ i , h , 1+ t ]∩[ m ↓, f ]-eq iS ⦃ u ⦄
  | inl (w , _) = {!!}
[ i , 1+ h , O ]∩[ m ↓, f ]-eq iS =
  [ i , h , Hom-size i h ]∩[ m ↓, f ]-eq (shape-from-next-h iS)
[ i , O , O ]∩[ .O ↓, f ]-eq iS ⦃ inl idp ⦄ = Shape= idp idp idp

[ i , h , 1+ t ]∩[ m ↑, f ]-eq iS = {!!}
[ i , 1+ h , O ]∩[ m ↑, f ]-eq iS@(shape-conds hcond (inr O<Hom-size)) ⦃ u ⦄ =
  [ i , h , Hom-size i h ]∩[ m ↑, f ]-eq iS' ⦃ tr (m ≤_) ((! p) ∙ q) u ⦄
  where
    iS' : is-shape i h (Hom-size i h)
    iS' = shape-from-next-h iS

    p : 1+ h == height (norm↑ i (1+ h) O iS)
    p = norm↑-nonfull i (1+ h) O iS O<Hom-size

    q : 1+ h == height (norm↑ i h (Hom-size i h) iS')
    q = norm↑-full i h iS' (S≤→< hcond)
[ .(1+ h) , 1+ h , O ]∩[ m ↑, f ]-eq iS@(shape-conds (inl idp) (inl _)) =
  [ 1+ h , h , Hom-size (1+ h) h ]∩[ m ↑, f ]-eq (shape-from-next-h iS)
[ i , 1+ h , O ]∩[ m ↑, f ]-eq iS@(shape-conds (inr x) (inl p)) =
  {!!}
[ .O , O , O ]∩[ m ↑, f ]-eq (shape-conds (inl idp) tcond₁) =
  [ O , O , O ]∩[ m ↓, f ]-eq (empty-shape O)
[ i , O , O ]∩[ m ↑, f ]-eq (shape-conds (inr _) (inl t=max)) = {!!}
[ i , O , O ]∩[ m ↑, f ]-eq (shape-conds (inr _) (inr t<max)) =
  [ i , O , O ]∩[ m ↓, f ]-eq (empty-shape i)

[ i , h , 1+ t ]∩[ m , f ]-eq iS = {!!}
[ i , 1+ h , O ]∩[ m , f ]-eq iS ⦃ u ⦄ =
  [ i , h , Hom-size i h ]∩[ m ↑, f ]-eq iS' ⦃ tr (m ≤_) p u ⦄
  where
    iS' = shape-from-next-h iS
    p = norm↑-full i h iS' (S≤→< (hcond iS))
[ i , O , O ]∩[ .O , f ]-eq iS ⦃ inl idp ⦄ = idp
