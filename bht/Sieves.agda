{--- Sieves in "nice enough" index categories ---}

{-# OPTIONS --without-K #-}

open import bht.NiceIndexCategory
open import Arithmetic
open import Fin renaming (to-ℕ to Fin-ℕ)

module bht.Sieves {i} ⦃ I : NiceIndexCategory {i} ⦄ where

open NiceIndexCategory I

{- Initial segment sieves -}

-- Throughout this development, a "sieve" is an initial segment sieve.
-- t is the *number* of maps in the topmost level Hom h b.

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
             → {m : ℕ} → {b ∸ h == m}
             → Σ[ h' ∈ ℕ ] (h' ≤ b) × (1 ≤ Hom-size h' b)
incr-level b h {O} = b , lteE , <→S≤ Hom-id-size
incr-level b h {1+ m} {p} with Hom-size (1+ h) b ≟-ℕ O
... | inl Hom-size=0 = incr-level b (1+ h) {m} {∸-move-S-l b h p}
... | inr Hom-size≠0 = 1+ h , <→S≤ (∸→< p) , <→S≤ (≠O→O< Hom-size≠0)

incr-sieve : Sieve → Sieve
incr-sieve ((b , h , t) , iS@(sieve-conds hcond tcond)) with hcond | tcond
... | inl h=b | _ = (b , h , t) , iS
... | inr h<b | inr t<max = (b , h , 1+ t) , is-sieve-next-t iS t<max
... | inr h<b | inl t=max = (b , h' , 1) , sieve-conds h'cond 1cond'
                             where
                               next-level : Σ[ h' ∈ ℕ ] (h' ≤ b) × (1 ≤ Hom-size h' b)
                               next-level = incr-level b h {b ∸ h} {idp}
                               h' = fst next-level
                               h'cond = 2nd next-level
                               1cond' = 3rd next-level

module incr-sieve-Properties where
  b-of-incr : (s : Sieve) → b-of-sieve (incr-sieve s) == b-of-sieve s
  b-of-incr ((b , h , t) , (sieve-conds hcond tcond)) with hcond | tcond
  ... | inl h=b | _ = idp
  ... | inr h<b | inr t<max = idp
  ... | inr h<b | inl t=max = idp

  h-of-incr-t<max : ∀ b h t iS
                    → t < Hom-size h b
                    → h-of-sieve (incr-sieve ((b , h , t) , iS)) == h
  h-of-incr-t<max b h t (sieve-conds hcond tcond) t<max with tcond
  ... | inl t=max = ⊥-elim (<-to-≠ t<max t=max)
  ... | inr _ with hcond
  ...            | inl _ = idp
  ...            | inr _ = idp

open incr-sieve-Properties


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

topmost-[_,_,_,_]-map-in-img-of?_ :
  (b h : ℕ) (t : ℕ₊) (iS : is-sieve b h (to-ℕ t)) {m : ℕ} (f : Hom m b)
  → Dec (Σ[ g ∈ Hom h m ] (f ◦ g == Hom-idx h b (t −1 , ≤→−1< (tcond iS))))
                                    -- t arrows in the (h → b) level, so the
                                    -- topmost one has index (t-1).
topmost-[ b , h , t , iS ]-map-in-img-of? f =
  Σ-Hom? (λ g → f ◦ g == Hom-idx h b (t −1 , ≤→−1< (tcond iS))) (λ g → _ ≟-Hom _)

[_,_,_]∩[_,_] : (b h t : ℕ)
                → (m : ℕ) (f : Hom m b)
                → is-sieve b h t
                → Sieve

[ b , h , 1+ t ]∩[ m , f ] iS
 with topmost-[ b , h , pos (1+ t) , iS ]-map-in-img-of? f
... | inl  in-img = incr-sieve ([ b , h , t ]∩[ m , f ] (is-sieve-prev-t iS))
... | inr ¬in-img = [ b , h , t ]∩[ m , f ] (is-sieve-prev-t iS)

[ b , O , O ]∩[ m , f ] iS = (m , O , O) , is-sieve-bh0 (O≤ m)

[ b , 1+ h , O ]∩[ m , f ] iS =
  [ b , h , Hom-size h b ]∩[ m , f ] (sieve-conds (S≤→≤ (hcond iS)) lteE)

module ∩-Properties where
  b-of-∩ : ∀ b h t {m} {f} iS
           → b-of-sieve ([ b , h , t ]∩[ m , f ] iS) == m
  b-of-∩ b h (1+ t) {m} {f} iS
   with topmost-[ b , h , pos (1+ t) , iS ]-map-in-img-of? f
  ... | inl  in-img = let iS' : is-sieve b h t
                          iS' = is-sieve-prev-t iS
                      in b-of-incr ([ b , h , t ]∩[ m , f ] iS')
                         ∙ b-of-∩ b h t iS'
  ... | inr ¬in-img = b-of-∩ b h t (is-sieve-prev-t iS)
  b-of-∩ b O O iS = idp
  b-of-∩ b (1+ h) O iS = b-of-∩ b h (Hom-size h b) (is-sieve-prev-h iS)

  [_,_,_]∩[_,_]◦-≼ :
    (b h : ℕ) (t : ℕ₊) (m : ℕ) (f : Hom m b) {iS : is-sieve b h (to-ℕ t)}
    → (g g' : Hom h m) → g' ≼ g
    → f ◦ g ≼ Hom-idx h b (t −1 , ≤→−1< (tcond iS))
    → f ◦ g' ≼ Hom-idx h b (t −1 , ≤→−1< (tcond iS))
  [ b , h , t ]∩[ m , f ]◦-≼ g g' = ≼-trans ∘ ◦-monotone'

  {-
  Need something like
    g ≼ Hom-idx h m (t' - 1) ↔ f ◦ g ≼ Hom-idx h b (t - 1)
  where [b, h, t]∩[m, f] == (m, h, t').

  Note: this *requires* the level of the intersection to be h.

  Remark: will we in fact need to generalize to an order not just on (Hom h b)
  for fixed b, h, but instead on pairs (h, t) for fixed b?
  -}

  [_,_,_]∩[_,_]-⊆-lem :
    (b h : ℕ) (t : ℕ₊) (m : ℕ) (f : Hom m b) (iS : is-sieve b h (to-ℕ t))
    {t' : ℕ₊} {iS' : is-sieve m h (to-ℕ t')}
    (p : [ b , h , to-ℕ t ]∩[ m , f ] iS == (m , h , to-ℕ t') , iS')
    (g : Hom h m)
    → let t'-1 : Fin (Hom-size h m)
          t'-1 = (t' −1) , ≤→−1< (tcond iS')

          t−1 : Fin (Hom-size h b)
          t−1 = (t −1) , ≤→−1< (tcond iS) in
      g ≼ Hom-idx h m (t'-1)
    → f ◦ g ≼ Hom-idx h b (t−1)

  [ b , h , t ]∩[ m , f ]-⊆-lem iS {t'} {iS'} p g g≼ = {!!}

  private
    -- Need this for h-of-∩:
    ∩-unc : ((((b , h , t) , iS) , m , f) :
                Σ[ ((b , h , t) , iS) ∈ Sieve ] Σ[ m ∈ ℕ ] Hom m b)
              → Sieve
    ∩-unc (((b , h , t) , iS) , m , f) = [ b , h , t ]∩[ m , f ] iS


  h-of-∩ : ∀ b h t {m} {f} iS
           → h-of-sieve ([ b , h , t ]∩[ m , f ] iS) ≤ h

  h-of-∩ b h (1+ t) {m} {f} iS
   with topmost-[ b , h , pos (1+ t) , iS ]-map-in-img-of? f
  ... | inl in-img
        with [ b , h , t ]∩[ m , f ] (is-sieve-prev-t iS)
           | inspect ∩-unc (((b , h , t) , is-sieve-prev-t iS) , m , f)
           | h-of-∩ b h t {m} {f} (is-sieve-prev-t iS)
           ---
  ...      | (b' , h' , t') , iS'
           | ▹ eq
           | inl h'=h = inl hlem
                        :> (h-of-sieve (incr-sieve ((b' , h' , t') , iS')) ≤ h)
                                                -- ↳ == [ b , h , t ]∩[ m , f ] _
             where
               {-
                           b
                           ↑ ↖ f
                 Hom-idx t | ∘ m
                           | ↗ t̃
                           h (= h')
               -}
               t̃ : Hom h m
               t̃ = fst in-img

               f◦t̃ : f ◦ t̃ == Hom-idx h b (t , _)
               f◦t̃ = snd in-img

               b'=m : b' == m
               b'=m = b' =⟨ ap b-of-sieve (! eq) ⟩
                      b-of-sieve ([ b , h , t ]∩[ m , f ] _) =⟨ b-of-∩ b h t _ ⟩
                      m =∎

               Hom-size-h'b'-hm : Hom-size h' b' == Hom-size h m
               Hom-size-h'b'-hm = ap (λ □ → Hom-size □ b' ) h'=h
                                  ∙ ap (Hom-size h) b'=m

               t'<max : t' < Hom-size h m
               {-
               Have that t' ≤ Hom-size h m.

               If t' = Hom-size h m, then
                 "t̃ is in the initial segment sieve (b', h', t')",
               which is [b, h, t]∩[m, f]; i.e.
                 Hom-ord t̃ < t'.
               [Lemma: `f : Hom x y → Hom-ord f < Hom-size x y`]

               Since
                 Hom-ord t̃ < t',
               we have that
                 f ◦ t̃ ≼ f ◦ Hom-idx (t' - 1), (t' > 0 since Hom h m contains t̃)
               and thus
                 t = Hom-ord (f ◦ t̃) ≤ Hom-ord (f ◦ Hom-idx (t' - 1)),
               ⇔ Hom-idx t ≼ f ◦ Hom-idx (t' - 1).

               Recall what the intersection [b, h, t]∩[m, f] computes:

               If S is an initial segment sieve of shape (b, h, t) and
               f ∶ Hom m b, then the sieve
                 S ∙ f = {g : Hom i m | 0 ≤ i ≤ m, f ◦ g ∈ S}
               is also an initial segment sieve (of height ≤ h):
               ∙ For i < h and g : Hom i m, f ◦ g : Hom i b ∈ S, and
               ∙ for i = h and g : Hom h m, if f ◦ g ∈ S then for all
                 g' : Hom h m s.t. g' ≼ g,  we have that f ◦ g' ≼ f ◦ g, and
                 since S is an initial segment sieve we must have
                 f ◦ g' ∈ S.
               In terms of sieve shapes, this last point says:
                 g : Hom h m
                 → Hom-ord (f ◦ g) < t
                 → g' : Hom h m
                 → Hom-ord g' ≤ Hom-ord g
                 → Hom-ord (f ◦ g') < t
                   ↳ = Hom-ord (f ◦ g') ≤ t - 1
                     = f ◦ g' ≼ Hom-idx h b (t - 1)

               ?g? : Hom h m
               Hom-ord (f ◦ ?g?) < t -- Hom-ord (f ◦ Hom-idx h m (t' - 1)) < t
               → t̃ : Hom h m
               → Hom-ord t̃ ≤ Hom-ord ?g? -- Hom-ord t̃ ≤ t' - 1 = (Hom-size h m) - 1
                                         -- So ?g? := Hom-idx h m (t' - 1)
               → f ◦ t̃ ≼ Hom-idx h b (t - 1)
                 ↳ Hom-idx h b t

               !!! Maybe need something saying that
                 t-of-sieve ([b,h,t]∩[m,f])
               is the LUB on

               [b, h, t]∩[m, f] is meant to give the *shape* of S ∙ f.
               -}
               t'<max = {!!}

               hlem : h-of-sieve (incr-sieve ((b' , h' , t') , iS')) == h
               hlem = h-of-incr-t<max
                        b' h' t' iS'
                        (tr (t' <_) (! Hom-size-h'b'-hm) t'<max)
                      ∙ h'=h
           ---
  ...      | (b' , h' , t') , iS'
           | ▹ eq
           | inr h'<h = {!!}
                      :> (h-of-sieve (incr-sieve ((b' , h' , t') , iS')) ≤ h)

  h-of-∩ b h (1+ t) {m} {f} iS
      | inr ¬in-img = h-of-∩ b h t (is-sieve-prev-t iS)

  h-of-∩ b   O    O iS = lteE
  h-of-∩ b (1+ h) O iS = lteSR (h-of-∩ b h (Hom-size h b) (is-sieve-prev-h iS))

  h-of-∩' : ∀ {b h t} iS {m} {f}
            → (i : ℕ) → h ≤ i
            → h-of-sieve ([ b , h , t ]∩[ m , f ] iS) ≤ i
  h-of-∩' {b} {h} {t} iS {_} {f} i icond = ≤-trans (h-of-∩ b h t iS) icond

  {-
  h-of-incr-∩-≤ : ∀ b h t {m} {f} iS
                  → h-of-sieve (incr-sieve ([ b , h , t ]∩[ m , f ] iS)) ≤ h
  h-of-incr-∩-≤ b h (1+ t) {m} {f} iS
   with topmost-[ b , h , pos (1+ t) , iS ]-map-in-img-of? f
  ... | inl  in-img = {!!}
        :> (h-of-sieve (incr-sieve
             (incr-sieve ([ b , h , t ]∩[ m , f ] (is-sieve-prev-t iS)))) ≤ h)
  ... | inr ¬in-img = h-of-incr-∩-≤ b h t (is-sieve-prev-t iS)
  h-of-incr-∩-≤ b O O {O} {f} iS = inl idp
  h-of-incr-∩-≤ b O O {1+ m} {f} iS
   with O≤ (Hom-size O (1+ m))
  ... | inl Hom-size-0-Sm=0 = {!this doesn't work, it's always ≥ 1; but maybe we
  can fix this with an extra condition!}
  ... | inr Hom-size-0-Sm>0 = inl idp
  h-of-incr-∩-≤ b (1+ h) O {m} {f} iS =
    ≤→≤S (h-of-incr-∩-≤ b h (Hom-size h b) (is-sieve-prev-h iS))
  -}

  {- Previous attempt
  h-of-incr-∩-≤ b h t {m} {f} iS
    with [ b , h , t ]∩[ m , f ] iS | inspect ∩-unc ((b , h , t , m) , f , iS )
  ... | (b' , h' , t') , (sieve-conds hcond' tcond') | ▹ eq
        with hcond'
  ...   | inl h'=b' = tr (λ □ → h-of-sieve □ ≤ h) eq (h-of-∩-≤ b h t iS)
                      -- incr-sieve([b, h, t]∩[m, f] iS)
                      -- ≡ incr-sieve((b', h', t'), _)
                      -- ≡ (b', h', t') ≡ [b, h, t]∩[m, f] iS.
                      -- So we can use h-of-∩-≤ b h t.
  ...   | inr h'<b'
          with tcond'
  ...     | inr t'<tmax' = tr (λ □ → h-of-sieve □ ≤ h) eq (h-of-∩-≤ b h t iS)
  ...     | inl t'=tmax'
            with Hom-size (1+ h') b' ≟-ℕ O
  ...       | inl Hom-size=0 = {!!}
  ...       | inr Hom-size≠0 = {!!}
            {-
            ⊢ fst (incr-level b' h' {b' ∸ h'} {idp}) ≤ h
            From h'<b' get (b' ∸ h' == 1+ _), so
              fst (incr-level b' h' {b' ∸ h'} {idp})
              == fst (incr-level b' h' {1+ _} {idp})
            depends on
              Hom-size (1+ h') b' ≟-ℕ O.

            + Hom-size (1+ h') b' ≠ O,
              fst (incr-level ...) ≡ 1+ h'.
            -}
  -}
