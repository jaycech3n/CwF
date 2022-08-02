{-# OPTIONS --without-K #-}

open import SuitableSemicategories

module ShapeRestriction ⦃ I : SuitableSemicategory ⦄ where
open SuitableSemicategory I

open import ShapeNormalization public


[_,_,_]⊙[_,_] : (i h t : ℕ) (m : ℕ) (f : Hom i m) → is-shape i h t → Shape
⊙-apex : ∀ i h t iS {m} f → apex ([ i , h , t ]⊙[ m , f ] iS) == m

-- Temporary
open import DSM _≟-ℕ_

factors-cumul : ∀ {i h m} → (t : Fin (Hom-size i h)) → Hom i m → DSHom m h
factors-cumul t f g = to-Bool (idx-of (g ◦ f) ≤?-Fin t)

-- end temp

[ i , h , 1+ t ]⊙[ m , f ] iS with [t] factors-through? f
  where [t] = Hom[ i , h ]# (t , S≤→< (tcond iS))
[ i , h , 1+ t ]⊙[ m , f ] iS | inl (w , w◦f=[t]) =
  norm↓ m h new-width (shape-conds (inr (Hom-inverse m h w)) width-cond)
  -- I think we can also choose to normalize up (in which case don't forget to
  -- normalize the empty case too), as long as we're consistent.

  -- temporarily hidden
  -- (m , h , {!!}) , {!!}
  where
  incr-width : Σ[ t ∈ ℕ ] t ≤ Hom-size m h
  incr-width = size (factors-cumul (t , S≤→< (tcond iS)) f)

  new-width = fst incr-width
  width-cond = snd incr-width
  {- temporarily hidden
    iS' = shape-from-next-t iS
    prev-⊙ = [ i , h , t ]⊙[ m , f ] iS'

    -- Claim 1:
    norm↑-prev-⊙-apex : apex (norm↑-unc prev-⊙) == m
    norm↑-prev-⊙-apex = norm↑-unc-apex prev-⊙ ∙ ⊙-apex i h t iS' {m} f

    -- Claim 2:
    norm↑-prev-⊙-height : height (norm↑-unc prev-⊙) == h
    norm↑-prev-⊙-height = {!!}

    t' = width (norm↑-unc prev-⊙)

    t'cond : t' ≤ Hom-size m h
    t'cond =
      tr (λ □ → t' ≤ Hom-size □ h) norm↑-prev-⊙-apex
        (tr (λ □ → t' ≤ Hom-size (apex (norm↑-unc prev-⊙)) □) norm↑-prev-⊙-height
          (tcond (snd (norm↑-unc prev-⊙))))

    [t'] : Hom m h
    [t'] = Hom[ m , h ]# (t' , {!t'cond!})

    #-factors = #-Hom[ m , h ]-from {!!} {!!} {!!}
   -}
[ i , h , 1+ t ]⊙[ m , f ] iS | inr no =
  [ i , h , t ]⊙[ m , f ] (shape-from-next-t iS)
[ i , 1+ h , O ]⊙[ m , f ] iS =
  [ i , h , Hom-size i h ]⊙[ m , f ] (shape-from-next-h iS)
[ i , O , O ]⊙[ m , f ] iS = (m , O , O) , empty-shape m -- do you want to normalize up?

⊙-apex i h (1+ t) iS f with [t] factors-through? f
  where [t] = Hom[ i , h ]# (t , S≤→< (tcond iS))
⊙-apex i h (1+ t) iS f | inl _ = {!-- no problem!}
⊙-apex i h (1+ t) iS f | inr _ = ⊙-apex i h t (shape-from-next-t iS) f
⊙-apex i (1+ h) O iS f = ⊙-apex i h (Hom-size i h) (shape-from-next-h iS) f
⊙-apex i O O iS {m} f = idp

shape-lemma : ∀ i h t iS {m} f → m ≤ height (norm↑ i h {i ∸ h} {idp} t iS) -- should this be norm↑?
  → [ i , h , t ]⊙[ m , f ] iS == norm↓ m m O (degen-shape m m lteE)
    -- and this too? And normalize the LHS too?
shape-lemma i h (1+ t) iS f u with [t] factors-through? f
  where [t] = Hom[ i , h ]# (t , S≤→< (tcond iS))
shape-lemma i h (1+ t) iS f u | inl (w , _) = {!!}
shape-lemma i h (1+ t) iS f u | inr _ =
  shape-lemma i h t (shape-from-next-t iS) f {!!}
shape-lemma i (1+ h) O iS f u =
  shape-lemma i h (Hom-size i h) (shape-from-next-h iS) f {!-- this is okay!}
shape-lemma i O O iS f u = {!-- this is okay!}
