{--- Sieves in "nice enough" index categories ---}

{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import bht.NiceIndexCategory
open import Arithmetic
open import Fin

module bht.Sieves {i} ⦃ I : NiceIndexCategory {i} ⦄ where

open NiceIndexCategory I

{- Initial segment sieves -}

-- Throughout this development, a "sieve" is an initial segment sieve.
-- t is the *number* of maps in the topmost level (h → b).

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

sieve-dim : Sieve → ℕ
sieve-dim ((_ , h , _) , _) = h

Sieve= : {s@(t , _) s'@(t' , _) : Sieve}
         → fst t == fst t' → 2nd t == 2nd t' → 3rd t == 3rd t' → s == s'
Sieve= idp idp idp = pair= idp (prop-path is-sieve-is-prop _ _)

is-sieve-bh0 : ∀ {b h} → h ≤ b → is-sieve b h O
is-sieve-bh0 {b} {h} h≤b = sieve-conds h≤b (O≤ (Hom-size h b))

is-sieve-prev-t : ∀ {b h t} → is-sieve b h (1+ t) → is-sieve b h t
is-sieve-prev-t (sieve-conds hcond tcond) = sieve-conds hcond (S≤→≤ tcond)

is-sieve-next-t : ∀ {b h t} → is-sieve b h t → t < Hom-size h b
                  → is-sieve b h (1+ t)
is-sieve-next-t (sieve-conds hcond tcond) t<tmax = sieve-conds hcond (<→S≤ t<tmax)

is-sieve-bhtmax : ∀ {b h} → h ≤ b → is-sieve b h (Hom-size h b)
is-sieve-bhtmax hcond = sieve-conds hcond lteE

is-sieve-prev-h : ∀ {b h} → is-sieve b (1+ h) O → is-sieve b h (Hom-size h b)
is-sieve-prev-h iS = is-sieve-bhtmax (S≤→≤ (hcond iS))

incr-level : (b h : ℕ)
             → {m : ℕ} → {b ∸ h == m}
             → Σ[ h' ∈ ℕ ] (h' ≤ b) × (1 ≤ Hom-size h' b)
incr-level b h {O} = b , lteE , <→S≤ Hom-id-size
incr-level b h {1+ m} {p} = ⊔-rec
                              (λ Hom-size=0 → incr-level b (1+ h) {m} {∸-move-S-l b h p})
                              (λ Hom-size≠0 → 1+ h , <→S≤ (∸→< p) , <→S≤ (≠O→O< Hom-size≠0))
                              (Hom-size (1+ h) b ≟-ℕ O)

incr-sieve : Sieve → Sieve
incr-sieve ((b , h , t) , iS@(sieve-conds hcond tcond)) with hcond | tcond
... | inl h=b | _ = (b , h , t) , iS
... | inr h<b | inr t<tmax = (b , h , 1+ t) , is-sieve-next-t iS t<tmax
... | inr h<b | inl t=tmax = (b , h' , 1) , sieve-conds h'cond 1cond'
                             where
                               next-level : Σ[ h' ∈ ℕ ] (h' ≤ b) × (1 ≤ Hom-size h' b)
                               next-level = incr-level b h {b ∸ h} {idp}
                               h' = fst next-level
                               h'cond = 2nd next-level
                               1cond' = 3rd next-level

{- Sieve intersection -}

topmost-[_,_,_,_]-map-in-img-of?_ :
  (b h : ℕ) ((pos t ⦃ O<t ⦄) : ℕ₊) (iS@(sieve-conds _ tcond) : is-sieve b h t)
  {m : ℕ} (f : Hom m b)
  → Dec (Σ[ g ∈ Hom h m ] (f ◦ g ≈ Hom-idx (ℕ-pred t , <→ℕ-pred< t O<t tcond)))
                                           -- t arrows in the (h → b) level, so
                                           -- the topmost one has index (t-1).
topmost-[ b , h , pos t ⦃ O<t ⦄ , iS@(sieve-conds _ tcond) ]-map-in-img-of? f =
  Σ-Hom? (λ g → f ◦ g ≈ Hom-idx (ℕ-pred t , <→ℕ-pred< t O<t tcond)) (λ g → _ ≈? _)

-- [ b, h, t ]∩[ m, f ] calculates the shape of the intersection of the
-- (b, h, t)-initial segment sieve with the principal sieve generated by
-- f : Hom m b.
[_,_,_]∩[_,_] : (b h t : ℕ)
                → (m : ℕ) (f : Hom m b)
                → is-sieve b h t
                → Sieve

-- This recursion still works if there is some Hom-size h b = 0
[ b , h , 1+ t ]∩[ m , f ] iS@(sieve-conds hcond tcond)
  with topmost-[ b , h , pos (1+ t) , iS ]-map-in-img-of? f
... | inl  in-img = incr-sieve ([ b , h , t ]∩[ m , f ] (is-sieve-prev-t iS))
... | inr ¬in-img = [ b , h , t ]∩[ m , f ] (is-sieve-prev-t iS)

[ b , O , O ]∩[ m , f ] iS = (m , O , O) , is-sieve-bh0 (O≤ m)

[ b , 1+ h , O ]∩[ m , f ] (sieve-conds hcond _) =
  [ b , h , Hom-size h b ]∩[ m , f ] (sieve-conds (S≤→≤ hcond) lteE)


∩-dim≤ : ∀ {b h t} iS {m} {f}
         → (i : ℕ) → h ≤ i
         → sieve-dim ([ b , h , t ]∩[ m , f ] iS) ≤ i
∩-dim≤ {b} {h} {t} iS {_} {f} i icond = ≤-trans (∩-dim≤-aux b h t iS) icond
  where
  ∩-dim≤-aux : ∀ b h t iS {m} {f}
               → sieve-dim ([ b , h , t ]∩[ m , f ] iS) ≤ h

  ∩-dim≤-aux b h (1+ t) iS {f = f}
    with topmost-[ b , h , pos (1+ t) , iS ]-map-in-img-of? f
  ... | inl  in-img = {!--probably need the corresponding lemma for incr-sieve!}
  ... | inr ¬in-img = ∩-dim≤-aux b h t (is-sieve-prev-t iS)

  ∩-dim≤-aux b   O    O iS = lteE
  ∩-dim≤-aux b (1+ h) O iS = lteSR (∩-dim≤-aux b h (Hom-size h b) (is-sieve-prev-h iS))
