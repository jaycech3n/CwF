{-# OPTIONS --without-K --allow-unsolved-metas #-}

module Fin where

open import Prelude public
open import Arithmetic public

private
  variable
    ℓ : ULevel


to-ℕ : ∀ {n} → Fin n → ℕ
to-ℕ = fst


{- Equality, inequality -}

Fin= : ∀ {n} {i j : Fin n} → to-ℕ i == to-ℕ j → i == j
Fin= {_} {.(fst j) , fstj<n} {j} idp = pair= idp (prop-path <-is-prop _ _)

Fin=-is-prop : ∀ {n} {i j : Fin n} → is-prop (i == j)
Fin=-is-prop {_} {i} {j} = has-level-apply Fin-is-set i j

Fin1-is-prop : is-prop (Fin 1)
has-level-apply Fin1-is-prop (i , i<1) (j , j<1) =
  has-level-in (Fin= (<1→=O i i<1 ∙ !(<1→=O j j<1)) , λ p → prop-path Fin=-is-prop _ _)

Fin1-has-all-paths : has-all-paths (Fin 1)
Fin1-has-all-paths i j = prop-path Fin1-is-prop _ _

Fin=-elim : ∀ {n} {i j : Fin n} → i == j → fst i == fst j
Fin=-elim {n} {_ , _} {.(_ , _)} idp = idp

_<-Fin_ : ∀ {n} (i j : Fin n) → Type₀
i <-Fin j = to-ℕ i < to-ℕ j

_≤-Fin_ : ∀ {n} (i j : Fin n) → Type₀
i ≤-Fin j = to-ℕ i ≤ to-ℕ j

_<?-Fin_ : ∀ {n} → Decidable (_<-Fin_ {n})
(i , _) <?-Fin (j , _) = i <? j

_≤?-Fin_ : ∀ {n} → Decidable (_≤-Fin_ {n})
(i , _) ≤?-Fin (j , _) = i ≤? j

≤-Fin-trans : ∀ {n} {i j k : Fin n} → i ≤-Fin j → j ≤-Fin k → i ≤-Fin k
≤-Fin-trans (inl idp) (inl idp) = inl idp
≤-Fin-trans (inr u) (inl idp) = inr u
≤-Fin-trans (inl idp) (inr v) = inr v
≤-Fin-trans (inr u) (inr v) = inr (<-trans u v)

abstract
  Fin-trichotomy : ∀ {k} (i j : Fin k) → (i == j) ⊔ (i <-Fin j) ⊔ (j <-Fin i)
  Fin-trichotomy (m , m<k) (n , n<k) = Fin-trichotomy-aux m n m<k n<k
    where
    Fin-trichotomy-aux : ∀ {k} (m n : ℕ) (m<k : m < k) (n<k : n < k)
                         →   ((m , m<k) == (n , n<k))
                           ⊔ ((m , m<k) <-Fin (n , n<k))
                           ⊔ ((n , n<k) <-Fin (m , m<k))
    Fin-trichotomy-aux O O _ _ = inl (Fin= idp)
    Fin-trichotomy-aux O (1+ n) _ _ = inr (inl (O<S n))
    Fin-trichotomy-aux (1+ m) O _ _ = inr (inr (O<S m))
    Fin-trichotomy-aux (1+ m) (1+ n) Sm<k Sn<k
     with Fin-trichotomy-aux m n (<-trans ltS Sm<k) (<-trans ltS Sn<k)
    ... | inl m=n = inl (Fin= (ap S (Fin=-elim m=n)))
    ... | inr (inl m<n) = inr (inl (<-ap-S m<n))
    ... | inr (inr n<m) = inr (inr (<-ap-S n<m))


{- Proof by enumeration -}

∀-Fin-extend : ∀ {n} {P : Fin (1+ n) → Type ℓ}
               → ((i : Fin n) → P (Fin-S i))
               → P (n , ltS)
               → ∀ i → P i
∀-Fin-extend {n = O} {P} _ PO _ = tr P (Fin1-has-all-paths _ _) PO
∀-Fin-extend {n = 1+ n} {P} f PSn (i , i<) =
   case (<S→≤ i<)
        (λ{ idp → tr P (Fin= idp) PSn })
        (λ i<Sn → tr P (Fin= idp) (f (i , i<Sn)))

∀-Fin? : ∀ {n} (P : Fin n → Type ℓ)
         → ((i : Fin n) → Dec (P i))
         → Dec ((i : Fin n) → P i)
∀-Fin? {n = O} P _ = inl (λ ())
∀-Fin? {n = 1+ n} P ∀Fin-Sn-Dec-P =
 if (∀-Fin? (P ∘ Fin-S) (∀Fin-Sn-Dec-P ∘ Fin-S))
    (λ ∀Fin-n-P → if (∀Fin-Sn-Dec-P (n , ltS))
                     (λ  Pn → inl (∀-Fin-extend ∀Fin-n-P Pn))
                     (λ ¬Pn → inr λ ∀Fin-Sn-P → ¬Pn (∀Fin-Sn-P (n , ltS))))
    (λ ¬∀Fin-n-P → inr λ ∀Fin-Sn-P → ¬∀Fin-n-P (∀Fin-Sn-P ∘ Fin-S))

Σ-Fin? : ∀ {n} (P : Fin n → Type ℓ)
         → ((i : Fin n) → Dec (P i))
         → Dec (Σ[ i ∈ Fin n ] P i)
Σ-Fin? {n = 0} _ _ = inr (λ ())
Σ-Fin? {n = 1} P ∀Fin-Sn-Dec-P =
  if (∀Fin-Sn-Dec-P 0)
     (λ  P0 → inl (0 , P0))
     (λ ¬P0 → inr λ{ ((O , ltS) , P0) → ¬P0 P0
                     ; ((1+ _ , ltSR ()) , _)})
Σ-Fin? {n = 2+ n} P ∀Fin-Sn-Dec-P =
  if (Σ-Fin? (P ∘ Fin-S) (∀Fin-Sn-Dec-P ∘ Fin-S))
     (λ{ (i , Pi) → inl ((Fin-S i) , Pi) })
     (λ ¬ΣFin-n-P →
       if (∀Fin-Sn-Dec-P (1+ n , ltS))
          (λ  PSn → inl ((1+ n , ltS) , PSn))
          (λ ¬PSn → inr
             λ{ ((i , i<2+n) , Pi) →
                ⊔-elim
                  (λ i≤Sn →
                     ⊔-elim
                       (λ i=Sn → ¬PSn (tr P (Fin= i=Sn) Pi))
                       (λ i<Sn → ¬ΣFin-n-P ((i , i<Sn) , (tr P (Fin= idp) Pi)))
                       i≤Sn)
                  (λ Sn<i → ¬-< (≤→<→< (<→S≤ Sn<i) i<2+n))
                  (ℕ-trichotomy' i (1+ n)) }))

-- Deciding fibers of maps between finite types
Fin-hfiber-dec : ∀ {m n} (f : Fin m → Fin n) (j : Fin n) → Dec (hfiber f j)
Fin-hfiber-dec {O} {n} f j = inr ((≮O _) ∘ snd ∘ fst)
Fin-hfiber-dec {1+ m} {n} f j =
  if (Fin-hfiber-dec (f ∘ Fin-S) j)
     (λ{ (x@(i , i<m) , fi=j) → inl (Fin-S x , ap f (Fin= idp) ∙ fi=j) })
     (λ h → if (f (m , ltS) ≟-Fin j)
               (λ fm=j → inl ((m , ltS) , fm=j))
               (λ fm≠j → inr λ{ ((i , i<Sm) , fi=j) →
                                ⊔-elim
                                  (λ i=m →
                                    fm≠j (ap f (Fin= (! i=m)) ∙ fi=j))
                                  (λ i<m  →
                                    h ((i , i<m) , ap f (Fin= idp) ∙ fi=j))
                                  (<S→≤ i<Sm) }))


{- Counting -}

-- The number of (i : Fin n) satisfying (P i)
#-Fin : ∀ {n} (P : Fin n → Type ℓ)
        → ((i : Fin n) → Dec (P i))
        → Fin (1+ n)
#-Fin {n = O} P d = 0 , ltS
#-Fin {n = 1+ n} P d =
  {!(if (d (n , ltS)) (λ _ → 1) λ _ → 0) +
    #-Fin {n = n} (P ∘ Fin-S) (d ∘ Fin-S)!}
