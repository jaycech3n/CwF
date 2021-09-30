module Fin where

open import Prelude public
open import Arithmetic public

private
  variable
    ℓ : ULevel

-- Equality on Fin

Fin=-intro : ∀ {n} {i j : Fin n} → fst i == fst j → i == j
Fin=-intro {_} {.(fst j) , fstj<n} {j} idp = pair= idp (prop-path <-is-prop _ _)

Fin=-is-prop : ∀ {n} {i j : Fin n} → is-prop (i == j)
Fin=-is-prop {_} {i} {j} = has-level-apply Fin-is-set i j

Fin1-is-prop : is-prop (Fin 1)
has-level-apply Fin1-is-prop (i , i<1) (j , j<1) =
  has-level-in (Fin=-intro (<1→=O i i<1 ∙ !(<1→=O j j<1)) , λ p → prop-path Fin=-is-prop _ _)

Fin1-has-all-paths : has-all-paths (Fin 1)
Fin1-has-all-paths i j = prop-path Fin1-is-prop _ _

-- Proof by exhaustion

∀-Fin-extend : ∀ {n} {P : Fin (1+ n) → Type ℓ}
               → ((i : Fin n) → P (Fin-S i))
               → P (n , ltS)
               → ∀ i → P i
∀-Fin-extend {n = O}    {P} _ PO  _ = tr P (Fin1-has-all-paths _ _) PO
∀-Fin-extend {n = 1+ n} {P} f PSn (i , i<)
  with <S-≤ i<
... | inl i==Sn = tr P (Fin=-intro (! i==Sn)) PSn
... | inr i<Sn  = tr P (Fin=-intro idp) (f (i , i<Sn))

∀-Fin? : ∀ {n} (P : Fin n → Type ℓ)
         → ((i : Fin n) → Dec (P i))
         → Dec ((i : Fin n) → P i)
∀-Fin? {n = O} P _ = inl (λ ())
∀-Fin? {n = 1+ n} P ∀Fin-Sn-Dec-P
  with ∀-Fin? (P ∘ Fin-S) (∀Fin-Sn-Dec-P ∘ Fin-S)
... | inl  ∀Fin-n-P = ⊔-elim
                        (λ  Pn → inl (∀-Fin-extend ∀Fin-n-P Pn))
                        (λ ¬Pn → inr (λ ∀Fin-Sn-P → ¬Pn (∀Fin-Sn-P (n , ltS))))
                        (∀Fin-Sn-Dec-P (n , ltS))
... | inr ¬∀Fin-n-P = inr λ ∀Fin-Sn-P → ¬∀Fin-n-P (∀Fin-Sn-P ∘ Fin-S)
