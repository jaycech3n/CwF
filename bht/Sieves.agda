-- Sieves in "nice enough" index categories

{-# OPTIONS --without-K --termination-depth=2 #-}

open import bht.NiceIndexCategory
open import Arithmetic
open import Fin

module bht.Sieves {i} ⦃ C : NiceIndexCategory {i} ⦄ where

open NiceIndexCategory C

-- Throughout this development, a "sieve" is an initial segment sieve.
-- t is the *number* of maps in the topmost level (h → b).

record is-sieve (b h t : ℕ) : Type₀ where
  constructor sieve-conds
  field
    hcond : h ≤ b
    tcond : t ≤ Hom-size h b

module _ where
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

Sieve= : {s@(t , _) s'@(t' , _) : Sieve}
         → fst t == fst t' → 2nd t == 2nd t' → 3rd t == 3rd t' → s == s'
Sieve= idp idp idp = pair= idp (prop-path is-sieve-is-prop _ _)

get-h : Sieve → ℕ
get-h ((_ , h , _) , _) = h

is-sieve-bh0 : ∀ {b h} → h ≤ b → is-sieve b h O
is-sieve-bh0 {b} {h} h≤b = sieve-conds h≤b (O≤ (Hom-size h b))

is-sieve-prev-t : ∀ {b h t} → is-sieve b h (1+ t) → is-sieve b h t
is-sieve-prev-t (sieve-conds hcond tcond) = sieve-conds hcond (S≤→≤ tcond)

is-sieve-next-t : ∀ {b h t} → is-sieve b h t → t < Hom-size h b
                  → is-sieve b h (1+ t)
is-sieve-next-t (sieve-conds hcond tcond) t<tmax = sieve-conds hcond (<→S≤ t<tmax)

-- Double-check these incr functions
incr-level : ∀ b h → h ≤ b → Σ[ h' ∈ ℕ ] (h' ≤ b) × (1 ≤ Hom-size h' b)
incr-level b h (inl h=b) = b , inl idp , <→S≤ Hom-id-size
incr-level b h (inr h<b) = ⊔-rec
                             (λ Hom-size=0 → incr-level b (1+ h) (<→S≤ h<b))
                             (λ Hom-size≠0 → 1+ h , <→S≤ h<b , <→S≤ (≠O→O< Hom-size≠0))
                             (Hom-size (1+ h) b ≟-ℕ O)

incr-sieve : Sieve → Sieve
incr-sieve ((b , h , t) , iS@(sieve-conds hcond tcond)) with hcond | tcond
... | inl h=b | _ = (b , h , t) , iS
... | inr h<b | inr t<tmax = (b , h , 1+ t) , is-sieve-next-t iS t<tmax
... | inr h<b | inl t=tmax = (b , h' , 1) , (sieve-conds h'cond 1cond')
                             where
                               next-level : Σ[ h' ∈ ℕ ] (h' ≤ b) × (1 ≤ Hom-size h' b)
                               next-level = incr-level b h hcond
                               h' = fst next-level
                               h'cond = 2nd next-level
                               1cond' = 3rd next-level
{-
first-is-sieve : (b h : ℕ) → h ≤ b → is-sieve b h 1
first-is-sieve n k k≤n = sieve-conds k≤n (binom≥1 (1+ n) (1+ k) (≤-ap-S k≤n))

last-is-sieve : (n k : ℕ) → k ≤ n → is-sieve n k (binom (1+ n) (1+ k))
last-is-sieve n k k≤n = sieve-conds ⦃ binom>O (1+ n) (1+ k) (≤-ap-S k≤n) ⦄
                                    k≤n lteE

prev-is-sieve-k : {n k : ℕ} (iS : is-sieve n (1+ k) 1)
                  → is-sieve n k (binom (1+ n) (1+ k))
prev-is-sieve-k {n} {k} (sieve-conds Sk≤n _) = last-is-sieve n k (≤-trans lteS Sk≤n)

sieve-increment : (n k t : ℕ) → is-sieve n k t → Sieve
sieve-increment n k t iS@(sieve-conds k≤n t≤binom) with k≤n | t≤binom
... | inl k==n | _            = (n , k , t) , iS
... | inr k<n  | inl t==binom = (n , 1+ k , 1) , first-is-sieve _ _ (<→S≤ k<n)
... | inr k<n  | inr t<binom  = (n , k , 1+ t) , sieve-conds k≤n (<→S≤ t<binom)


{- Face maps -}

is-increasing : ∀ {m n} → (Fin m → Fin n) → Type₀
is-increasing f = ∀ {i j} → fst i < fst j → fst (f i) < fst (f j)

_→+_ : ℕ → ℕ → Type₀
m →+ n = Σ (Fin (1+ m) → Fin (1+ n)) is-increasing

fun-of : ∀ {m n} → (m →+ n) → Fin (1+ m) → Fin (1+ n)
fun-of (f , _) = f

_img-⊆_ : ∀ {m m' n} (f : m →+ n) (g : m' →+ n) → Type₀
_img-⊆_ {m} f g = (i : Fin (1+ m)) → hfiber (fun-of g) (fun-of f i)

_img-⊆?_ : ∀ {m m' n} (f : m →+ n) (g : m' →+ n) → Dec (f img-⊆ g)
_img-⊆?_ f g = ∀-Fin? _ (λ i → Fin-hfiber-dec (fun-of g) (fun-of f i))

map-of-index : (n k t : ℕ) → is-sieve n k t → (k →+ n)
map-of-index n k t = {!!}
-}


{- Sieve intersection -}

topmost-[_,_,_,_]-map-in-img-of?_ :
  (b h : ℕ) ((t , O<t) : ℕ₊) (iS@(sieve-conds _ tcond) : is-sieve b h t)
  {m : ℕ} (f : Hom m b)
  → Dec (Σ[ g ∈ Hom h m ] (f ◦ g ≈ Hom-idx (ℕ-pred t , <→ℕ-pred< t O<t tcond)))
                                           -- t arrows in the (h → b) level, so
                                           -- the topmost one has index (t-1).
topmost-[ b , h , (t , O<t) , iS@(sieve-conds _ tcond) ]-map-in-img-of? f =
  Σ-Hom? (λ g → f ◦ g ≈ Hom-idx (ℕ-pred t , <→ℕ-pred< t O<t tcond)) (λ g → _ ≈? _)

-- [ b, h, t ]∩[ m, f ] calculates the shape of the intersection of the
-- (b, h, t)-initial segment sieve with the principal sieve generated by
-- f : Hom m b.
[_,_,_]∩[_,_] : (b h t : ℕ)
                → (m : ℕ) (f : Hom m b)
                → is-sieve b h t
                → Sieve

-- This is okay if there is some Hom-size h b = 0
[ b , h , 1+ t ]∩[ m , f ] iS@(sieve-conds hcond tcond) =
  ⊔-rec
    (λ  in-img → incr-sieve {!!})
    (λ ¬in-img → [ b , h , t ]∩[ m , f ] (is-sieve-prev-t iS))
    (topmost-[ b , h , (1+ t , O<S t) , iS ]-map-in-img-of? f)

[ b , O , O ]∩[ m , f ] iS = (m , O , O) , is-sieve-bh0 (O≤ m)

[ b , 1+ h , O ]∩[ m , f ] (sieve-conds hcond _) =
  [ b , h , Hom-size h b ]∩[ m , f ] (sieve-conds (S≤→≤ hcond) (inl idp))

{-
[ b , O , 1+ t ]∩[ m , f ] iS =
  ⊔-elim
    (λ (g , f◦g≈t) → incr-sieve ([ b , O , t ]∩[ m , f ] (is-sieve-prev-t iS)))
    (λ ¬in-img → [ b , O , t ]∩[ m , f ] (is-sieve-prev-t iS))
    (topmost-[ b , O , (1+ t , O<S t) , iS ]-map-in-img-of? f)

[ b , 1+ h , 1+ t ]∩[ m , f ] iS = {!!}
-}

{-
∩-not-none-tmax : (n k : ℕ) (iS : is-sieve n k (binom (1+ n) (1+ k)))
                  {m : ℕ} (f : m →+ n)
                  → [ n , k , binom (1+ n) (1+ k) ]∩[ m , f ] iS ≠ none

∩-not-none-k : (n k t : ℕ) (iS : is-sieve n (1+ k) t)
               {m : ℕ} (f : m →+ n)
               → [ n , 1+ k , t ]∩[ m , f ] iS ≠ none

[ n , O , 1 ]∩[ m , f ] iS
  with [ n , O , 1 , first-is-sieve n O (O≤ n) ]-face-in-img? f
...  | inl  in-f = some ((m , O , 1) , first-is-sieve m O (O≤ m)) -- base case
...  | inr ¬in-f = none

[ n , O , 2+ t ]∩[ m , f ] iS
  with [ n , O , 2+ t , iS ]-face-in-img? f
     | [ n , O , 1+ t ]∩[ m , f ] (prev-is-sieve-t iS)
...  | inl  in-f | inl ((n' , k' , t') , iS') = some (sieve-increment n' k' t' iS')
...  | inl  in-f | none = some ((m , O , 1) , (first-is-sieve m O (O≤ m))) -- base case
...  | inr ¬in-f | s = s

[ n , 1+ k , 1 ]∩[ m , f ] iS
  with [ n , 1+ k , 1 , iS ]-face-in-img? f
     | [ n , k , binom (1+ n) (1+ k) ]∩[ m , f ] (prev-is-sieve-k iS)
     | ∩-not-none-tmax n k (prev-is-sieve-k iS) f
...  | inl  in-f | inl ((n' , k' , t') , iS') | _ = some (sieve-increment n' k' t' iS')
...  | inl  in-f | none | w = some (⊥-elim (w idp)) -- this will never happen
...  | inr ¬in-f | s    | _ = s

[ n , 1+ k , 2+ t ]∩[ m , f ] iS
  with [ n , 1+ k , 2+ t , iS ]-face-in-img? f
     | [ n , 1+ k , 1+ t ]∩[ m , f ] (prev-is-sieve-t iS)
     | ∩-not-none-k n k (1+ t) (prev-is-sieve-t iS) f
...  | inl  in-f | inl ((n' , k' , t') , iS') | _ = some (sieve-increment n' k' t' iS')
...  | inl  in-f | none | w = some (⊥-elim (w idp)) -- this will never happen
...  | inr ¬in-f | s    | _ = s

∩-not-none-tmax n k iS {m} f = {!!}

∩-not-none-k n k (1+ O) iS {m} f
  with [ n , 1+ k , 1 , iS ]-face-in-img? f
     | [ n , k , binom (1+ n) (1+ k) ]∩[ m , f ] (prev-is-sieve-k iS)
     | ∩-not-none-tmax n k (prev-is-sieve-k iS) f
...  | inl  in-f | inl _ | _ = some≠none
...  | inl  in-f | none  | _ = some≠none
...  | inr ¬in-f | _     | w = w

∩-not-none-k n k (2+ t) iS {m} f
  with [ n , 1+ k , 2+ t , iS ]-face-in-img? f
     | [ n , 1+ k , 1+ t ]∩[ m , f ] (prev-is-sieve-t iS)
     | ∩-not-none-k n k (1+ t) (prev-is-sieve-t iS) f
...  | inl  in-f | inl _ | _ = some≠none
...  | inl  in-f | none  | _ = some≠none
...  | inr ¬in-f | _     | w = w
-}
