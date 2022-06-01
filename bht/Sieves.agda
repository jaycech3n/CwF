{--- Sieves in "nice enough" index categories ---}

{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import bht.NiceIndexCategory
open import Arithmetic
open import Fin renaming (to-ℕ to Fin-ℕ)

module bht.Sieves {i} ⦃ I : NiceIndexCategory {i} ⦄ where

open NiceIndexCategory I


{- Initial segment sieves -}

-- Throughout this development, a "sieve" is an initial segment sieve.
-- t is the number of maps in the topmost level Hom h b.

record is-sieve (b h t : ℕ) : Type₀ where
  constructor sieve-conds
  field
    hcond : h ≤ b
    tcond : t ≤ Hom-size h b

open is-sieve

is-sieve= : ∀ {b h t} {iS iS' : is-sieve b h t}
            → hcond iS == hcond iS'
            → tcond iS == tcond iS'
            → iS == iS'
is-sieve= idp idp = idp

is-sieve-is-prop : ∀ {b h t} → is-prop (is-sieve b h t)
is-sieve-is-prop = all-paths-is-prop
                   λ{(sieve-conds hcond tcond)
                     (sieve-conds hcond' tcond')
                   → is-sieve= (prop-path ≤-is-prop hcond hcond')
                               (prop-path ≤-is-prop tcond tcond')}

Sieve : Type₀
Sieve = Σ[ s ∈ ℕ × ℕ × ℕ ]
          let b = fst s
              h = 2nd s
              t = 3rd s
          in is-sieve b h t

b-of-sieve : Sieve → ℕ
b-of-sieve ((b , _ , _) , _) = b

h-of-sieve : Sieve → ℕ
h-of-sieve ((_ , h , _) , _) = h

t-of-sieve : Sieve → ℕ
t-of-sieve ((_ , _ , t) , _) = t

sieve-cond-of : (((b , h , t) , _) : Sieve) → is-sieve b h t
sieve-cond-of (_ , iS) = iS

Sieve= : {s@(t , _) s'@(t' , _) : Sieve}
         → fst t == fst t' → 2nd t == 2nd t' → 3rd t == 3rd t' → s == s'
Sieve= idp idp idp = pair= idp (prop-path is-sieve-is-prop _ _)

Sieve=h : {s s' : Sieve} → s == s' → h-of-sieve s == h-of-sieve s'
Sieve=h idp = idp

is-sieve-bh0 : ∀ {b h} → h ≤ b → is-sieve b h O
is-sieve-bh0 {b} {h} h≤b = sieve-conds h≤b (O≤ (Hom-size h b))

is-sieve-prev-t : ∀ {b h t} → is-sieve b h (1+ t) → is-sieve b h t
is-sieve-prev-t (sieve-conds hcond tcond) = sieve-conds hcond (S≤→≤ tcond)

is-sieve-next-t : ∀ {b h t} → is-sieve b h t → t < Hom-size h b
                  → is-sieve b h (1+ t)
is-sieve-next-t (sieve-conds hcond _) t<max = sieve-conds hcond (<→S≤ t<max)

is-sieve-bhtmax : ∀ {b h} → h ≤ b → is-sieve b h (Hom-size h b)
is-sieve-bhtmax hcond = sieve-conds hcond lteE

is-sieve-prev-h : ∀ {b h} → is-sieve b (1+ h) O → is-sieve b h (Hom-size h b)
is-sieve-prev-h iS = is-sieve-bhtmax (S≤→≤ (hcond iS))

incr-level : (b h : ℕ)
             → {d : ℕ} → {b ∸ h == d}
             → Σ[ h' ∈ ℕ ] (h' ≤ b) × (1 ≤ Hom-size h' b)
incr-level b h {O} = b , lteE , <→S≤ Hom-id-size
incr-level b h {1+ d} {p} with O <? Hom-size (1+ h) b
... | inl O<Hom-size = 1+ h , <→S≤ (∸→< p) , <→S≤ O<Hom-size
... | inr O=Hom-size = incr-level b (1+ h) {d} {∸-move-S-l b h p}

private
  incr-level-ub :
    ∀ m h' h {d} {p} → h' < h → O < Hom-size h m
    → fst (incr-level m h' {d} {p}) ≤ h

  incr-level-ub m h' h {O} {p} h'<h _ = ≤→<→≤ (∸→≤ p) h'<h
  incr-level-ub m h' h {1+ d} h'<h O<Hom-size
   with O <? Hom-size (1+ h') m
  ... | inl _ = <→S≤ h'<h
  ... | inr O=Hom-size'
        with <→S≤ h'<h
  ...      | inl idp = ⊥-elim (O=Hom-size' O<Hom-size)
  ...      | inr u = incr-level-ub m (1+ h') h {d} u O<Hom-size

incr-sieve : Sieve → Sieve
incr-sieve ((b , h , t) , iS@(sieve-conds hcond tcond)) with hcond | tcond
... | inl h=b | _         = (b , h , t) , iS
... | inr h<b | inr t<max = (b , h , 1+ t) , is-sieve-next-t iS t<max
... | inr h<b | inl t=max = (b , h' , 1) , sieve-conds h'cond 1cond'
                            where
                              next-level :
                                Σ[ h' ∈ ℕ ] (h' ≤ b) × (1 ≤ Hom-size h' b)
                              next-level = incr-level b h {b ∸ h} {idp}
                              h' = fst next-level
                              h'cond = 2nd next-level
                              1cond' = 3rd next-level

module incr-sieve-Properties where
  b-of-incr : (s : Sieve) → b-of-sieve (incr-sieve s) == b-of-sieve s
  b-of-incr ((b , h , t) , sieve-conds (inl _) _) = idp
  b-of-incr ((b , h , t) , sieve-conds (inr _) (inl _)) = idp
  b-of-incr ((b , h , t) , sieve-conds (inr _) (inr _)) = idp

  h-of-incr-t<max : ∀ b h t iS
                    → t < Hom-size h b
                    → h-of-sieve (incr-sieve ((b , h , t) , iS)) == h
  h-of-incr-t<max b h t (sieve-conds hcond (inl t=max)) t<max =
    ⊥-elim (<-to-≠ t<max t=max)
  h-of-incr-t<max b h t (sieve-conds (inl _) (inr _)) _ = idp
  h-of-incr-t<max b h t (sieve-conds (inr _) (inr _)) _ = idp

open incr-sieve-Properties


{- Sieve normalization -}

abstract
  decr-level : (b h : ℕ) → h ≤ b
               → Σ[ h' ∈ ℕ ] (h' == O) ⊔ ((h' ≤ h) × (O < Hom-size h' b))
  decr-level b   O    _    = O , inl idp
  decr-level b (1+ h) Sh≤b with O <? Hom-size h b
  ... | inl O<Hom-size = h , inr (inr ltS , O<Hom-size)
  ... | inr O=Hom-size
        with decr-level b h (S≤→≤ Sh≤b)
  ...      | h' , inl h'=0                 = h' , inl h'=0
  ...      | h' , inr (h'≤h , O<Hom-size') = h' , inr (≤→≤S h'≤h , O<Hom-size')

normalize : Sieve → Σ[ ((_ , h , t) , _) ∈ Sieve ] (O < h → O < t)
normalize s@((_ , _ , 1+ t) , _) = s , λ _ → O<S t
normalize s@((_ , O , O) , _) = s , λ x → x
normalize ((b , 1+ h , O) , iS) with decr-level b (1+ h) (hcond iS)
... | .O , inl idp =
        ((b , O , Hom-size O b)
        , is-sieve-bhtmax (O≤ b)) , ⊥-elim ∘ ¬-<
... | h' , inr (h'≤Sh , O<Hom-size) =
        ((b , h' , Hom-size h' b) , is-sieve-bhtmax (≤-trans h'≤Sh (hcond iS)))
        , λ _ → O<Hom-size

normalize-sieve : Sieve → Sieve
normalize-sieve = fst ∘ normalize

h-of-normalize : (s : Sieve) → h-of-sieve (normalize-sieve s) ≤ h-of-sieve s
h-of-normalize ((b , h , 1+ t) , iS) = inl idp
h-of-normalize ((b , O , O) , iS) = inl idp
h-of-normalize ((b , 1+ h , O) , iS) with decr-level b (1+ h) (hcond iS)
... | .O , inl idp = O≤ (1+ h)
... | h' , inr (u , _) = u

t-of-normalize : (s : Sieve)
                 → O < h-of-sieve (normalize-sieve s)
                 → O < t-of-sieve (normalize-sieve s)
t-of-normalize = snd ∘ normalize



{- Sieve level order -}

data [_,_]≼[_,_] (h' t' h t : ℕ) : Type₀ where
  on-h : h' < h           → [ h' , t' ]≼[ h , t ]
  on-t : h' == h → t' ≤ t → [ h' , t' ]≼[ h , t ]

Sieve≼-trans : ∀ {h i j t u v}
               → [ h , t ]≼[ i , u ]
               → [ i , u ]≼[ j , v ]
               → [ h , t ]≼[ j , v ]
Sieve≼-trans (on-h u) (on-h v) = on-h (<-trans u v)
Sieve≼-trans {h} (on-h u) (on-t idp _) = on-h u
Sieve≼-trans {j = j} (on-t idp u) (on-h v) = on-h v
Sieve≼-trans (on-t idp u) (on-t idp v) = on-t idp (≤-trans u v)

Sieve≼-idp : ∀ {h t} → [ h , t ]≼[ h , t ]
Sieve≼-idp = on-t idp (inl idp)

Sieve≼-St : ∀ {h t} → [ h , t ]≼[ h , 1+ t ]
Sieve≼-St = on-t idp (inr ltS)


{- Sieve intersection -

[ b, h, t ]∩[ m, f ] calculates the shape of the intersection of the
(b, h, t)-initial segment sieve S with the principal sieve generated by
f : Hom m b.

This intersection is the sieve
  S ∙ f = {g : Hom i m | 0 ≤ i ≤ h, f ◦ g ∈ S}
and is in fact also an initial segment sieve (of height ≤ h), since:
∙ For i < h and g : Hom i m, f ◦ g : Hom i b ∈ S, and
∙ for i = h and g : Hom h m, if f ◦ g ∈ S then for all g' : Hom h m s.t. g' ≼ g,
  we have that f ◦ g' ≼ f ◦ g, and since S is an initial segment sieve we must
  have f ◦ g' ∈ S.
-}

open ℕ₊ using (to-ℕ)

Hom-idx[_,_,_,_]-in-img-of?_ :
  (b h t : ℕ) (tcond : t < Hom-size h b) {m : ℕ} (f : Hom m b)
  → Dec (Σ[ g ∈ Hom h m ] (f ◦ g == Hom-idx h b (t , tcond)))
Hom-idx[ b , h , t , tcond ]-in-img-of? f =
  Σ-Hom? (λ g → f ◦ g == Hom-idx h b (t , tcond)) (λ g → _ ≟-Hom _)

[_,_,_]∩[_,_] : (b h t : ℕ)
                (m : ℕ) (f : Hom m b)
                → is-sieve b h t
                → Sieve
[ b , h , 1+ t ]∩[ m , f ] iS
 with Hom-idx[ b , h , t , S≤→< (tcond iS) ]-in-img-of? f
... | inl  in-img = incr-sieve ([ b , h , t ]∩[ m , f ] (is-sieve-prev-t iS))
... | inr ¬in-img = [ b , h , t ]∩[ m , f ] (is-sieve-prev-t iS)
[ b , O , O ]∩[ m , f ] iS = (m , O , O) , is-sieve-bh0 (O≤ m)
[ b , 1+ h , O ]∩[ m , f ] iS =
  [ b , h , Hom-size h b ]∩[ m , f ] (sieve-conds (S≤→≤ (hcond iS)) lteE)


module ∩-Properties where
  open ≺-Reasoning

  b-of-∩ : ∀ b h t {m} {f} iS
           → b-of-sieve ([ b , h , t ]∩[ m , f ] iS) == m
  b-of-∩ b h (1+ t) {m} {f} iS
   with Hom-idx[ b , h , t , S≤→< (tcond iS) ]-in-img-of? f
  ... | inl  in-img = let iS' : is-sieve b h t
                          iS' = is-sieve-prev-t iS in
                      b-of-incr ([ b , h , t ]∩[ m , f ] iS')
                      ∙ b-of-∩ b h t iS'
  ... | inr ¬in-img = b-of-∩ b h t (is-sieve-prev-t iS)
  b-of-∩ b O O iS = idp
  b-of-∩ b (1+ h) O iS = b-of-∩ b h (Hom-size h b) (is-sieve-prev-h iS)

  {-
  Need something like
    g ≼ Hom-idx h m (t' - 1) ↔ f ◦ g ≼ Hom-idx h b (t - 1)
  where [b, h, t]∩[m, f] == (m, h, t').

  Note: this *requires* the level of the intersection to be h.

  Remark: will we in fact need to generalize to an order not just on (Hom h b)
  for fixed b, h, but instead on pairs (h, t) for fixed b?
  -}

  [_,_,_]∩[_,_]◦-≼ :
    (b h : ℕ) (t : ℕ₊) (m : ℕ) (f : Hom m b) {iS : is-sieve b h (to-ℕ t)}
    (g g' : Hom h m)
    → g' ≼ g
    → f ◦ g ≼ Hom-idx h b (t −1 , ≤→−1< (tcond iS))
    → f ◦ g' ≼ Hom-idx h b (t −1 , ≤→−1< (tcond iS))
  [ b , h , t ]∩[ m , f ]◦-≼ g g' = ≼-trans ∘ ◦-monotone'


  private
    ∩-unc : ((((b , h , t) , iS) , m , f) :
                Σ[ ((b , h , t) , iS) ∈ Sieve ] Σ[ m ∈ ℕ ] Hom m b)
              → Sieve
    ∩-unc (((b , h , t) , iS) , m , f) = [ b , h , t ]∩[ m , f ] iS

  abstract
    h,t-of-∩ : (b h t : ℕ) {m : ℕ} (f : Hom m b) (iS : is-sieve b h t)
               → let S' = [ b , h , t ]∩[ m , f ] iS in
                 [ h-of-sieve S' , t-of-sieve S' ]≼[ h , t ]

    h,t-of-∩ b h (1+ t) {m} f iS
     with Hom-idx[ b , h , t , S≤→< (tcond iS) ]-in-img-of? f
    ... | inr ¬in-img = Sieve≼-trans (h,t-of-∩ b h t f (is-sieve-prev-t iS)) Sieve≼-St
    ... | inl in-img with
        -- Let [ b , h , t ]∩[ m , f ] = (b' , h' , t'),
            [ b , h , t ]∩[ m , f ] (is-sieve-prev-t iS)
          | inspect ∩-unc (((b , h , t) , (is-sieve-prev-t iS)) , m , f)
        -- then by induction, [ h' , t' ]≼[ h , t ].
          | h,t-of-∩ b h t f (is-sieve-prev-t iS)

        -- Want to show that [h,t]-of([ b, h, 1+t ]∩[ m, f ])≼[ h, 1+ t ].
        -- Have the following cases:
    ...   -- h' = b'
          | (b' , h' , t') , sieve-conds (inl h'=b') _
          | _
          | ih
            = Sieve≼-trans ih Sieve≼-St

    ...   {-
            h' < b' , t' = Hom-size h' b'
            h' < h
          -}
          | (b' , h' , .(Hom-size h' b')) , sieve-conds (inr h'<b') (inl idp)
          | ▹ eq
          | on-h h'<h
            = ⊔-rec
                {C = [ fst (incr-level b' h' {b' ∸ h'} {idp}) , 1 ]≼[ h , 1+ t ]}
                (λ incr-level=h → on-t incr-level=h (≤-ap-S (O≤ t)))
                (λ incr-level<h → on-h incr-level<h)
                (incr-level-ub b' h' h {b' ∸ h'} {idp}
                                       h'<h (Hom-size-witness g))
              where
                b'=m : b' == m
                b'=m = ap b-of-sieve (! eq) ∙ b-of-∩ b h t (is-sieve-prev-t iS)

                g : Hom h b'
                g = tr (Hom h) (! b'=m) (fst in-img)
    ...   {-
            h' < b' , t' = Hom-size h' b'
            h' = h , t' ≤ t
          -}
          | (b' , .h , .(Hom-size h b')) , sieve-conds (inr h<b') (inl idp)
          | ▹ eq
          | on-t idp t'≤t
            = {!-- C-u C-u C-c C-,!}
                -- This goal is unprovable; either there's a contradiction
                -- derivable from the hypotheses, or we need to change some
                -- definitions...

    ...   {-
            h' < b' , t' < Hom-size h' b'
            h' < h
          -}
          | (b' , h' , t') , sieve-conds (inr h'<b') (inr t'<max)
          | _
          | on-h h'<h
            = on-h h'<h

    ...   {-
            h' < b' , t' < Hom-size h' b'
            h' = h , t' ≤ t
          -}
          | (b' , h' , t') , sieve-conds (inr h'<b') (inr t'<max)
          | _
          | on-t h'=h t'≤t
            = on-t h'=h (≤-ap-S t'≤t)

    h,t-of-∩ b   O    O f iS = Sieve≼-idp
    h,t-of-∩ b (1+ h) O f iS = Sieve≼-trans (h,t-of-∩ b h (Hom-size h b) f
                                                      (is-sieve-prev-h iS))
                                            (on-h ltS)

  h-of-∩ : ∀ b h t {m} {f} iS
           → h-of-sieve ([ b , h , t ]∩[ m , f ] iS) ≤ h
  h-of-∩ b h t {f = f} iS with h,t-of-∩ b h t f iS
  ... | on-h u = inr u
  ... | on-t p _ = inl p

  t-of-∩ : ∀ b h t {m} {f} iS
           → let S' = [ b , h , t ]∩[ m , f ] iS in
             (level-cond : h-of-sieve S' == h)
           → t-of-sieve S' ≤ t
  t-of-∩ b h t {f = f} iS level-cond with h,t-of-∩ b h t f iS
  ... | on-h u = ⊥-elim (<-to-≠ u level-cond)
  ... | on-t _ u = u

  h-of-∩' : ∀ {b h t} iS {m} {f}
            → (i : ℕ) → h ≤ i
            → h-of-sieve ([ b , h , t ]∩[ m , f ] iS) ≤ i
  h-of-∩' {b} {h} {t} iS {_} {f} i icond = ≤-trans (h-of-∩ b h t iS) icond
