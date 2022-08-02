{-# OPTIONS --without-K #-}

{--- Sieve restriction

If S is a sieve under i and (f : Hom i m) then the restriction (S ⊙ f) of S
along f is the sieve under m given by
  S ⊙ f = { g : Hom m k | k : ℕ and (g ∘ f) ∈ S }.

If S is a linear sieve in a well oriented semicategory then so is S ⊙ f. We
define the shape restriction [i, h, t]⊙[m, f] (where S has shape (i, h, t)),
giving the shape of S ⊙ f.
-}

open import SuitableSemicategories

module SieveRestriction ⦃ I : WellOrientedSemicategory ⦄ where
open WellOrientedSemicategory I

open import Sieves public


{- Shape restriction -}

factors-cumul : ∀ {i h m} → (t : Fin (Hom-size i h)) → Hom i m → DSHom m h
factors-cumul t f g = to-Bool (idx-of (g ◦ f) ≤?-Fin t)

[_,_,_]⊙[_,_] : (i h t : ℕ) (m : ℕ) (f : Hom i m) → is-shape i h t → Shape
[ i , h , 1+ t ]⊙[ m , f ] iS

  {- Let (m, h, t') be the representative of (i, h, t)∙(m, f) of that form
  (claim: can always find such a ~-representative). Count the number k of
    g : Hom m h
  such that [t'] ≤ g and [t] = g ◦ f. Then set (i, h, 1+t)∙(m, f) := (m, h, t' +
  k).
  -}
 with Hom[ i , h ]# (t , S≤→< (tcond iS)) factors-through? f
... | inr no = [ i , h , t ]⊙[ m , f ] (shape-from-next-t iS)
... | inl (w , _) = (m , h , new-width) ,
                      shape-conds (inr (Hom-inverse m h w)) width-cond
      where
        incr-width : Σ[ t ∈ ℕ ] t ≤ Hom-size m h
        incr-width = size (factors-cumul (t , S≤→< (tcond iS)) f)

        new-width = fst incr-width
        width-cond = snd incr-width

[ i , 1+ h , O ]⊙[ m , f ] iS = [ i , h , Hom-size i h ]⊙[ m , f ]
                                  (full-shape i h (≤-trans lteS (hcond iS)))
[ i ,   O  , O ]⊙[ m , f ] iS = (m , O , O) , empty-shape m


{- Shape restriction describes linear sieve restriction -}

{-sieve-next-h-⊙ : ∀ i h iS {m} (f : Hom i m) →
  sieve[ i , h , Hom-size i h ] (shape-from-next-h iS) ⊙ f
  == sieve[ i , 1+ h , O ] iS ⊙ f
sieve-next-h-⊙ i h iS f = {!!}

sieve-⊙-shape : ∀ i h t iS {m} f
  → sieve-unc ([ i , h , t ]⊙[ m , f ] iS) == sieve[ i , h , t ] iS ⊙ f
sieve-⊙-shape i h (1+ t) iS f = {!!}
sieve-⊙-shape i (1+ h) O iS f =
  sieve-⊙-shape i h (Hom-size i h) (shape-from-next-h iS) f
  ∙ sieve-next-h-⊙ i h iS f
sieve-⊙-shape i O O iS {m} f =
  sieve-unc ([ i , O , O ]⊙[ m , f ] iS) =⟨ empty-sieve-eq m (empty-shape m) ⟩
  Ø =⟨ ! Ø-⊙ ⟩
  Ø ⊙ f =⟨ ! (empty-sieve-eq i iS) |in-ctx (_⊙ f) ⟩
  sieve[ i , O , O ] iS ⊙ f =∎-}


{- Shape of sufficiently small restrictions -}

shape-lemma : ∀ i h t iS {m} f → m ≤ norm-h i h t iS
  → [ i , h , t ]⊙[ m , f ] iS == norm m m O (degen-shape m m lteE)
shape-lemma i h (1+ t) iS {m} f u
 with Hom[ i , h ]# (t , S≤→< (tcond iS)) factors-through? f
... | inr x = shape-lemma i h t (shape-from-next-t iS) f {!!}
... | inl x = {!!}
shape-lemma i (1+ h) O iS {m} f u =
  shape-lemma i h (Hom-size i h) (shape-from-next-h iS) f u
shape-lemma i O O iS f u rewrite ≤O→=O u = idp
