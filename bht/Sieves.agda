{-# OPTIONS --without-K --allow-unsolved-metas #-}

{--- Sieves in Δ₊ ---

The development of shapes is completely independent of CwF's. It provides a
combinatorial setting that enables us to later define boundaries and
subsimplices.

# Idea

Assume a semisimplicial type (A₀, A₁, A₂) is given. Some examples of "triangle
complexes" that we can consider are:

(1) Σ(x y z : A₀).
     Σ(f : A₁ x y). Σ(g : A₁ y z). Σ(h : A₁ x z).
      A₂ f g h
    This is a full triangle.

(2) Σ(x y z : A₀). (A₁ x y) × (A₁ y z)
    This is a pair of composable lines.

(3) Σ(x y z : A₀). (A₁ x y) × (A₁ y z) × (A₁ x z)
    This is an unfilled triangle.

(4) Σ(x y : A₀). A₁ x y
    This is a single line.

Recall that (A₀, A₁, A₂) encodes a (strict) contravariant functor from an
initial segment of the category Δ₊ to the category of types. Let's write A for
this functor A : Δ₊ → U. From this point of view, the full triangle (1) encodes
the type of natural transformations Δ² → A, where Δ² is the obvious
representable functor a.k.a. Yoneda[2] a.k.a. the 2-simplex. The functor Λ²₁ is
a subfunctor of Δ²: intuitively, it is the simplex Δ² with the filler and one
face removed.

The example (2) above encodes the type of natural transformations Λ²₁ → A.

∂Δ² is the subfunctor of Δ² with only the filler removed. We call it the
"2-simplex boundary". The unfilled triangle (3) encodes the type of natural
transformations ∂Δ² → A.

Regarding example (4), Δ¹ is also a subfunctor of Δ², but not in a unique way -
a triangle has three edges.

Subfunctors of yoneda[2] can also be described as *sieves*
  https://ncatlab.org/nlab/show/sieve
under the object [2] (= Fin 3) in Δ₊. This is probably the easier way to think
about them. Every morphism into [2] gives one "component" and the sieve
condition expresses exactly that a component can only be present if all its
faces are.

Thinking of Δ², Λ²₁, and ∂Δ² as sieves also makes it easy to describe the
canonical injections that we have between them.  The sequence of injections
  Λ²₁ ↪ ∂Δ² ↪ Δ²
adds one component (morphism) to the sieve in each of the two steps.

The sieves of Δ₊ describe "raw shapes" of subsimplices. We can develop some
theory of these sieves without talking about semisimplicial types.

# Main challenge

Sieves are naturally structured in a non-linear way, but we eventually want to
use them to describe the shapes of nested Σ-types (see examples 1-4), which are
linear. Thus, we need to "linearise" the sieves in some form.

# Preliminaries

For natural numbers k,m, let φ : Fin (binom m k) → (Fin k →⁺ Fin m) be the
bijection between strictly increasing maps (denoted by →⁺) and their
cardinality; this gives a linear order.  From now on, we write `Fin k` for the
object [k-1] of Δ₊. We only consider k ≥ 1.

# The sieves of interest

The sieves that we are interested in can be described as triples (b,h,t) of
natural numbers, where h ≤ b and t ≤ binom b (h+1). The triple (b,h,t) is to be
interpreted as follows:

b (for "base") is the number of points (0-cells). In other words, (b,h,t)
  describes a sieve under the object (Fin b) in Δ₊. This means that the sieve
  (b,h,t) consists of morphisms (Fin i) →⁺ (Fin b) in Δ₊.

h (for "height") describes how many levels of the sieve are complete. For
  1 ≤ i ≤ h, every morphism (Fin i) →⁺ (Fin b) is in the sieve (b,h,t).

t (for "top", although there could be a better name) describes how many of the
  morphisms (Fin h+1) →⁺ (Fin b) are in the sieve. That's why
  0 ≤ t ≤ binom b (h+1), since the binominal coefficient describes the number of
  morphisms (Fin h+1) →⁺ (Fin b). The bijection φ (see Preliminaries above)
  tells us which t morphisms are in the sieve, namely φ(0), ..., φ(t-1).

# Calculations on sieves

We need to be able to calculate a subsieve of a given sieve.  Again, we only
need special subsieves of the special sieves of the form (b,h,t).

Note that the simplex Δⁱ⁻¹ is a (iterated) face, and thus a subsieve, of the
simplex Δᵇ⁻¹ as long as i < b, but not in a unique way; a morphism
  (Fin i) →⁺ (Fin b)
determines the embedding of Δⁱ⁻¹ into Δᵇ⁻¹. Using the notation above, Δᵇ⁻¹ can
be written as (b,b,0) and Δⁱ⁻¹ as (i,i,0). (b,h,t) is a subsieve of (b,b,0) in a
unique way.

Given (b,h,t) and f : (Fin i) →⁺ (Fin b), we want to calculate the intersection
of (b,h,t) and (i,i,0) as subsieves of Δᵇ⁻¹. We denote this intersection by
(b,h,t) ∩ f.

The cases are:
  (b,0,0) ∩ f = (i,0,0) -- degenerate case: (b,0,0) is empty.
    We probably need to return (i,0,0) to make the recursion
    work.
  (b,h+1,0) ∩ f =
    let
      (b',h',t') = (b,h,binom b h+1) ∩ f
    in
      if t' == binom b' h'+1 then (b',h'+1,0) else (b',h',t')
      -- note that the subsieves (b,h+1,0) and
      (b,h,binom b h+1) are the same. Probably we don't need
      to distinguish cases here, we can just return
      (b,h,binom b h+1) ∩ f  directly.
  (b,h,t+1) ∩ f =
    let
      (b',h',t') = (b,h,t) ∩ f
      x = if φ(t) ⊆ im(f) then 1 else 0
    in
      if t' == binom b' h'+1
         then (b',h'+1,x) else (b',h',t'+x)
  -- this is the main case. To calculate the intersection
     with a subsieve with "one more component", we remove
     that component (case given by recursion) and check
     whether that additional component should in fact be in
     the intersection.

At this point, it is non-obvious whether ∩ really calculates the intersection of
subsieves (and I probably got it wrong).  One issue is that (b,h,binom b h+1)
and (b,h+1,0) represent the same sieve, and it's quite unfortunate that we need
to convert them. Maybe we can abstract a bit by using a quotient.

In any case, we need to check carefully whether that algorithm calculates the
intersection. We don't need to formalise this proof; but if it's not true, then
the later development won't work.

# Properties

We need the following:

Lemma. Given a sieve (b,h,t) and an f : (Fin h+1 →⁺ Fin b) such that t ≤ φ⁻¹(f),
we have (b,h,t) ∩ f == (h+1,h,0).

Note: (h+1,h,0) represents the sieve ∂Δʰ.

# How to use this

The intended usage of sieves (not in this file) is as follows. Given a CwF, we
construct simultaneously:

SST : ℕ → Con
Sk : ((b,h,t) : Sieve) → (n : ℕ) → (n ≥ h+1) → Ty (SST n)

They are to be understood as:
SST n is the context (A₀ : U, A₁ : ..., ..., Aₙ₋₁ : ...).
Sk (3,2,0) 3 is example (3) above. It is equivalent to
Sk (3,1,3) 3.

---}

module bht.Sieves where

open import Arith

-- Increasing functions
_→⁺_ : ℕ → ℕ → Set
m →⁺ n = Σ (Fin m → Fin n)
           λ f → (i j : Fin m) → (fst i < fst j) → fst (f i) < fst (f j)

-- Would want to work with this, but termination issues.
-- https://github.com/agda/agda/issues/995
{-
record Sieve' : Set where
  field
    b : ℕ -- base
    h : ℕ -- height
    t : ℕ -- top
    h≤b : h ≤ b
    t≤binom : t ≤ binom b (S h)
-}

isSieve : ℕ × ℕ × ℕ → Set
isSieve (b , h , t) = (h ≤ b) × (t ≤ binom b (S h))

Sieve = Σ (ℕ × ℕ × ℕ) isSieve

get-b get-h get-t : Sieve → ℕ
get-b ((b , h , t) , p) = b
get-h ((b , h , t) , p) = h
get-t ((b , h , t) , p) = t

-- Normalise "down". Todo: formulate for Sieves.
normalise : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ
normalise (b , O , t) = (b , O , t)
normalise (b , S h , O) = (b , h , binom b (S h))
normalise (b , S h , S t) = (b , S h , S t)

-- We can also "normalise up" by using use ℕ-has-dec-eq.
-- Not sure whether we need it though (probably we do).


-- Switching between natural numbers and increasing functions.
decode : ∀ {k m} → Fin (binom m k) → k →⁺ m
decode = {!!}

encode : ∀ {k m} → (k →⁺ m) → Fin (binom m k)
encode = {!!}

-- Probably not needed:
decode∘encode : ∀ {k m} (f : k →⁺ m) → decode (encode f) == f
decode∘encode = {!!}

-- Pretty sure that this is needed:
encode∘decode : ∀ {k m} (t : Fin (binom m k)) → encode {m = m} (decode t) == t
encode∘decode = {!!}

-- Note: decode∘encode needs funext. But this is actually weird, semisimplicial
-- types shouldn't depend on funext. I think we might not need decode∘encode at
-- all!

module _ {m n b : ℕ} (g : m →⁺ b) (f : n →⁺ b) where

  -- Is the image of g contained in the image of f?
  _⊆₊_ : Set
  _⊆₊_ = (i : Fin m) → Σ (Fin n) λ j → (fst g i) == (fst f j)

  -- This property is decidable:
  _⊆₊?_ : Dec _⊆₊_
  _⊆₊?_ = {!!}


-- Adding a single component to a sieve. In most cases, this just increases t by
-- one.
add-component : Sieve → Sieve
add-component ((b , h , t) , p) =
  let
    t-max? : Dec (t == binom b (S h))
    t-max? = ℕ-has-dec-eq t (binom b (S h))
    h-max? : Dec (h == b)
    h-max? = ℕ-has-dec-eq h b
    Sh=b?  : Dec (S h == b)
    Sh=b?  = ℕ-has-dec-eq (S h) b
  in
    Coprod-rec
      (λ t-max →
        Coprod-rec
          (λ h-max → (b , h , t) , p) -- The sieve (b, b, 0) is already
                                      -- full. Don't add anything.
          (λ ¬h-max →
             Coprod-rec
               (λ Sh=b → (b , h , t) , p) -- Sieve (b, b-1, binom b b) is full;
                                          -- don't add anything.
               (λ ¬Sh=b → (b , S h , 1) ,
                            ( <-S≤ (≤-¬=-< (fst p) ¬h-max)
                            , <-S≤
                                (binom>O b (S (S h))
                                  (<-S≤
                                    (≤-¬=-<
                                      (<-S≤ (≤-¬=-< (fst p) ¬h-max)) ¬Sh=b)))))
               Sh=b?)
          h-max?)
      (λ ¬t-max → (b , h , S t) , (fst p , <-S≤ (≤-¬=-< (snd p) ¬t-max)))
      t-max?


-- Making all arguments explicit (makes the definition a bit nicer, but probably
-- not the usage):
[_,_,_,_]∩[_,_] : (b h t : ℕ) → (isSieve (b , h , t)) → (k : ℕ) → (k →⁺ b) → Sieve

[ b ,   h , S t , p ]∩[ k , f ] =
  let
    last-component : S h →⁺ b
    last-component = decode {S h} {b} (t , {!snd p!}) -- Note: not a
                                                      -- mistake. It's `t`, not
                                                      -- `S t`.
    sieve-without-last : Sieve
    sieve-without-last = [ b , h , t , (fst p , {!snd p!}) ]∩[ k , f ]
    add-new? : Dec (last-component ⊆₊ f)
    add-new? = last-component ⊆₊? f
  in
     Coprod-rec {A = last-component ⊆₊ f} {B = ¬ (last-component ⊆₊ f)} {C = Sieve}
       (λ  last⊆₊f → add-component sieve-without-last)
       (λ ¬last⊆₊f → sieve-without-last)
       add-new?
[ _ ,   O ,   O , _ ]∩[ k , f ] = (k , O , O) , (O≤ k) , (O≤ (binom k 1))
[ b , S h ,   O , p ]∩[ k , f ] = [ b , h , binom b (S h) , (S≤-≤ (fst p) , inl idp) ]∩[ {!!} , f ]

{- Lemma: If we have a big enough (but not too big!) bht-sieve and intersect it
   with a small enough representable sieve, we get a "matching object" (i.e. a
   "tetrahedron with a single component missing").
   Concretely:
   Given a sieve (b,h,t,_) and f : S h →⁺ b
   such that f is not part of (b , h , t , _), then
   (b,h,t) ∩ f == (h+1,h,0).
-}

∩-gives-matching : (((b , h , t) , p) : Sieve) (f : S h →⁺ b) → t ≤ S (fst (encode f)) →
  [ b , h , t , p ]∩[ S h , f ] == (S h , h , O) , (lteS , O≤ _)

∩-gives-matching = {!!} -- difficult but very important
