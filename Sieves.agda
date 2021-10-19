{-# OPTIONS --without-K --termination-depth=2 --allow-unsolved-metas #-}

module Sieves where

open import Arithmetic public
open import Fin public


{- Sieves -}

-- A sieve (n,k,t) describes the shape of partial k-skeleta of n-simplices in
-- which the first t k-faces are present.

record is-sieve (n k t : ℕ) : Type₀ where
  constructor sieve-conds
  field
    ⦃ tpos ⦄ : O < t
    kcond : k ≤ n
    tcond : t ≤ binom (1+ n) (1+ k)

module _ where
  open is-sieve
  is-sieve= : ∀ {n k t} {iS iS' : is-sieve n k t}
              → tpos iS == tpos iS'
              → kcond iS == kcond iS'
              → tcond iS == tcond iS'
              → iS == iS'
  is-sieve= idp idp idp = idp

is-sieve-is-prop : ∀ {n k t} → is-prop (is-sieve n k t)
is-sieve-is-prop = all-paths-is-prop
                   λ{(sieve-conds ⦃ tpos ⦄ kcond tcond)
                     (sieve-conds ⦃ tpos' ⦄ kcond' tcond')
                   → is-sieve= (prop-path <-is-prop tpos tpos')
                               (prop-path ≤-is-prop kcond kcond')
                               (prop-path ≤-is-prop tcond tcond')}

Sieve : Type₀
Sieve = Σ[ s ∈ ℕ × ℕ × ℕ ]
          let n = fst s
              k = 2nd s
              t = 3rd s
          in is-sieve n k t

Sieve= : {s@(t , _) s'@(t' , _) : Sieve}
         → fst t == fst t' → 2nd t == 2nd t' → 3rd t == 3rd t' → s == s'
Sieve= idp idp idp = pair= idp (prop-path is-sieve-is-prop _ _)

get-k : Sieve → ℕ
get-k ((_ , k , _) , _) = k

first-is-sieve : (n k : ℕ) → k ≤ n → is-sieve n k 1
first-is-sieve n k k≤n = sieve-conds k≤n (binom≥1 (1+ n) (1+ k) (≤-ap-S k≤n))

last-is-sieve : (n k : ℕ) → k ≤ n → is-sieve n k (binom (1+ n) (1+ k))
last-is-sieve n k k≤n = sieve-conds ⦃ binom>O (1+ n) (1+ k) (≤-ap-S k≤n) ⦄
                                    k≤n lteE

prev-is-sieve-k : {n k : ℕ} (iS : is-sieve n (1+ k) 1)
                  → is-sieve n k (binom (1+ n) (1+ k))
prev-is-sieve-k {n} {k} (sieve-conds Sk≤n _) = last-is-sieve n k (≤-trans lteS Sk≤n)

prev-is-sieve-t : {n k t : ℕ} → is-sieve n k (2+ t) → is-sieve n k (1+ t)
prev-is-sieve-t (sieve-conds k≤n St≤binom) = sieve-conds k≤n (≤-trans lteS St≤binom)

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


{- Subsieves and intersection -}

private
  [_,_,_,_]-face-in-img?_ : ∀ {m} (n k t : ℕ) (iS : is-sieve n k t) (f : m →+ n)
                            → Dec (map-of-index n k t iS img-⊆ f)
  [ n , k , t , iS ]-face-in-img? f = (map-of-index n k t iS) img-⊆? f

-- [n, k, t]∩[m, f] calculates the shape of the intersection of a face
-- map f : m →+ n with the sieve (n,k,t).

[_,_,_]∩[_,_] : (n k t : ℕ)
                → (m : ℕ) (f : m →+ n)
                → is-sieve n k t
                → Maybe Sieve

∩-not-none-tmax : (n k : ℕ) (iS : is-sieve n k (binom (1+ n) (1+ k)))
                  {m : ℕ} (f : m →+ n)
                  → [ n , k , binom (1+ n) (1+ k) ]∩[ m , f ] iS ≠ none

∩-not-none-k : (n k t : ℕ) (iS : is-sieve n (1+ k) t)
               {m : ℕ} (f : m →+ n)
               → [ n , 1+ k , t ]∩[ m , f ] iS ≠ none

[ n , O , 1+ O ]∩[ m , f ] iS
  with [ n , O , 1 , first-is-sieve n O (O≤ n) ]-face-in-img? f
...  | inl  in-f = some ((m , O , 1) , first-is-sieve m O (O≤ m)) -- base case
...  | inr ¬in-f = none

[ n , O , 2+ t ]∩[ m , f ] iS
  with [ n , O , 2+ t , iS ]-face-in-img? f
     | [ n , O , 1+ t ]∩[ m , f ] (prev-is-sieve-t iS)
...  | inl  in-f | inl ((n' , k' , t') , iS') = some (sieve-increment n' k' t' iS')
...  | inl  in-f | none = some ((m , O , 1) , (first-is-sieve m O (O≤ m))) -- base case
...  | inr ¬in-f | s = s

[ n , 1+ k , 1+ O ]∩[ m , f ] iS
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


{-
In particular, we need something like...

  [ n+1 , k , binom (n+2) (k+1) ]∩[ 

-}


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
