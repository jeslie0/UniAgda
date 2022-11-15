{-# OPTIONS --without-K --safe --no-import-sorts #-}
module UniAgda.Core.Types.Identity where

open import UniAgda.Core.Types.Universes

-- We define the identity type as an inductive type, and tell Agda
-- that it is the builtin identity.

-- * Identity Types
data _≡_ {i : Level} {A : Type i} (x : A) : A → Type i where
  refl : x ≡ x
infix 5 _≡_
_==_ = _≡_
{-# BUILTIN EQUALITY _≡_ #-}

-- We get both forms of path induction for free.
bpath-ind : {i j : Level} {A : Type i}
            (a : A) (C : (x : A) → a ≡ x → Type j) (c : C a refl)
            → (x : A) (p : a ≡ x) → C x p
bpath-ind a C c .a refl = c

path-ind : {i j : Level} {A : Type i}
           (C : (x y : A) → x ≡ y → Type j) (c : (x : A) → C x x refl)
         → (a b : A) → (p : a ≡ b) → C a b p
path-ind C c x .x refl = c x

-- * Groupoid Structure
-- Path types give rise to a groupoid structure on Types. Reflexivity
-- is proven by the refl map above, symmetry is proven here and
-- corresponds to inverses:
-- Lemma2.1.1
_^ : {i : Level} {A : Type i} {x y : A}
     (p : x ≡ y)
     → y ≡ x
refl ^ = refl
infix 30 _^

-- Transitivity is proven here and corresponds to concatenation.
-- Lemma2.1.2
_∘_ : ∀ {i} {A : Type i} {x y z : A}
      (p : x ≡ y) (q : y ≡ z)
      → x ≡ z
_∘_ refl q = q
infixr 20 _∘_

-- We will prove the groupoid properties in another section.
-- * Ap and Transport
-- We have that functions can be applied to paths.
-- Lemma2.2.1
ap : ∀ {i j} {A : Type i} {B : Type j} {x y : A}
     (f : A → B) (p : x ≡ y)
     → (f x ≡ f y)
ap f refl = refl

-- Transport gives us an operation on type families.
-- Lemma2.3.1
transport : ∀ {i j} {A : Type i} {x y : A}
            (P : A → Type j) (p : x ≡ y)
            → P x → P y
transport P refl x = x

syntax transport P p = p #[ P ]

-- The above give rise to dependant ap.
-- Lemma2.3.4
apD : ∀ {i j} {A : Type i} {x y : A} {P : A → Type j}
      (f : (x : A) → P x) → (p : x ≡ y)
      → (transport P p (f x)) ≡ (f y)
apD f refl = refl

-- * Higher transports
-- The higher groupoid nature allows us to treat functions not just as
-- functors, but \(\infty-\) functors. We define the second level of
-- this.
ap² : ∀ {i j} {A : Type i} {B : Type j} {x y : A} {p q : x ≡ y}
      (f : A → B) (r : p ≡ q)
      → ap f p ≡ ap f q
ap² f refl = refl

transport² : ∀ {i j} {A : Type i} {x y : A} {p q : x ≡ y}
             {P : A → Type j} (r : p ≡ q) (u : P x)
             → transport P p u ≡ transport P q u
transport² refl u = refl

apD² : ∀ {i j} {A : Type i} {P : A → Type j} {x y : A} {p q : x ≡ y}
       (f : (x : A) → P x) (r : p ≡ q)
       → apD f p ≡ transport² r (f x) ∘ (apD f q)
apD² f refl = refl
