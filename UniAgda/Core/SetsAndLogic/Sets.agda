{-# OPTIONS --without-K --no-import-sorts #-}
module UniAgda.Core.SetsAndLogic.Sets where

open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Functions
open import UniAgda.Core.Types.Identity
open import UniAgda.Core.Types.Sigma
open import UniAgda.Core.Types.Coproduct
open import UniAgda.Core.Types.W
open import UniAgda.Core.Types.Unit
open import UniAgda.Core.Types.Empty
open import UniAgda.Core.Types.Bool
open import UniAgda.Core.Types.Nat
open import UniAgda.Core.Types.FiniteSets

open import UniAgda.Core.PathAlgebra
open import UniAgda.Core.Homotopy
open import UniAgda.Core.Equivalences
open import UniAgda.Core.SetsAndLogic.ContrPropSet1Type

open import UniAgda.Core.PathSpaces.Coproduct
open import UniAgda.Core.PathSpaces.Identity
open import UniAgda.Core.PathSpaces.Nat
open import UniAgda.Core.PathSpaces.Sigma
open import UniAgda.Core.PathSpaces.Unit

open import UniAgda.Core.Axioms
open import UniAgda.Core.SetsAndLogic.Props

-- * Products of sets are sets
-- The product of two sets is also a set.
--  Example 3.1.5

Sigma-of-sets-is-set : ∀ {i j} {A : Type i} {B : A → Type j}
                       → (isSet A) → ((x : A) → isSet (B x))
                       → isSet (Σ[ x ∈ A ] B x)
Sigma-of-sets-is-set {B = B} H₁ H₂ (a , b) (a' , b') =
  equiv-with-prop
    (thm2-7-2 ^ᵉ)
    λ { (p1 , p2) (q1 , q2) → path-equiv-sigma
      ((H₁ a a' p1 q1 ,
      H₂ a' (transport B q1 b) b' (transport (λ z → transport B z b ≡ b') (H₁ a a' p1 q1) p2) q2))}

prod-of-sets-is-set : ∀ {i j} {A : Type i} {B : Type j}
                      → (isSet A) → (isSet B)
                      → (isSet (A × B))
prod-of-sets-is-set H₁ H₂ = Sigma-of-sets-is-set H₁ λ x → H₂

-- * Coproducts of sets are sets
-- The coproduct of two sets is a set.

coproduct-of-sets-is-set : ∀ {i j} {A : Type i} {B : Type j}
                           → isSet A → isSet B
                           → isSet (A + B)
coproduct-of-sets-is-set X Y (inl a) (inl a') =
  (equiv-base-Pi
    (thm2-12-5 a (inl a')))
    λ { (map-raise x) refl → ap (ap inl) (X a a x refl) }
coproduct-of-sets-is-set X Y (inl a) (inr b) =
  equiv-base-Pi
    (thm2-12-5 a (inr b))
    λ x ()
coproduct-of-sets-is-set X Y (inr b) (inl a) =
  equiv-base-Pi
    (a=b≃b=a oₑ thm2-12-5 a (inr b))
    λ x ()
coproduct-of-sets-is-set X Y (inr b) (inr b') =
  equiv-base-Pi
    (thm2-12-5ii b (inr b'))
    λ { (map-raise x) refl → ap (ap inr) (Y b b x refl)}

-- * Function types between sets are sets
--  Example3.1.6

fibs-are-sets-PI-is-set : ∀ {i j} {A : Type i} {B : A → Type j}
                          → ((x : A) → (isSet (B x)))
                          → (isSet ((x : A) → B x))
fibs-are-sets-PI-is-set H f g =
  equiv-with-prop
    (funextD-equiv ^ᵉ)
    λ { X Y → funextD λ a →
      H a (f a) (g a) (X a) (Y a)}


func-of-sets-is-set : ∀ {i j} {A : Type i} {B : Type j}
                      → (isSet B)
                      → (isSet (A → B))
func-of-sets-is-set H =
  fibs-are-sets-PI-is-set λ x → H

-- * Sets are 1-Types
--  Lemma3.1.8

private
  helper : ∀ {i} {A : Type i}
           → (f : isSet {i} A) → (x y : A) → (p q q' : x ≡ y) → (r : q ≡ q')
           → (f x y p q) ∘ r ≡ f x y p q'
  helper f x y p q q' r = (lemma2-11-2i _ r (f x y p q) ^ ) ∘ apD (λ q → f x y p q) r


sets-are-1types : ∀ {i} {A : Type i}
                  → isSet {i} A → is1type {i} A
sets-are-1types f x y p q r s = pq=r-to-q=p^r (f x y p p) r (f x y p q) (helper f x y p p q r) ∘ (pq=r-to-q=p^r (f x y p p) s (f x y p q) (helper f x y p p q s)) ^

-- * Results

isSet-is-prop : {i : Level}
                (A : Type i)
                → isProp (isSet A)
isSet-is-prop A f g = funextD λ {x → funextD λ x₁ → funextD λ x₂ → funextD λ x₃ → sets-are-1types f _ _ _ _ _ _}


-- Being a set is preserved by equivalence.

equiv-with-set : ∀ {i j} {A : Type i} {B : Type j}
                 → A ≃ B → isSet A
                 → isSet B
equiv-with-set (f , g , α , β , γ) F x y =
  equiv-with-prop {_} {_} {g x ≡ g y} {x ≡ y}
    (((ap g) ,
      (thm2-11-1 (isequiv-adjointify (f , (α , β))))) ^ᵉ)
    (F (g x) (g y))


-- If a type family has fibres valued in props and comes from a set, the total space is a set.

prop-fibres-totalspace-set : ∀ {i j} {A : Type i} {P : A → Type j}
                             → isSet A → ((a : A) → isProp (P a))
                             → isSet (Σ[ a ∈ A ] (P a))
prop-fibres-totalspace-set {i} {j} {A} {P} H f (a , X) (b , Y) =
  equiv-with-prop
  (thm2-7-2 ^ᵉ)
  (λ { (p , p') (q , q') →
    path-equiv-sigma
      ((H _ _ _ _) ,
      (props-are-sets (f b) _ _ _ _))})


-- * Unit is a set
-- The unit type is a set.
--  Example3.1.2

Unit-is-set : isSet Unit
Unit-is-set = props-are-sets λ { tt tt → refl}

-- * Empty is a set
-- The empty type is a set.
--  Example3.1.3

Empty-is-set : isSet Empty
Empty-is-set () y

-- * The natural numbers are a set
-- The natural numbers are a set, as their path space is either
-- contractible or empty.
--  Example3.1.4

ℕ-is-set : isSet ℕ
ℕ-is-set zero zero = equiv-with-prop (thm2-13-1 zero zero ^ᵉ) Unit-is-prop
ℕ-is-set zero (suc m) = equiv-with-prop (thm2-13-1 zero (suc m) ^ᵉ) λ x ()
ℕ-is-set (suc n) zero = equiv-with-prop (thm2-13-1 (suc n) zero ^ᵉ) λ x ()
ℕ-is-set (suc n) (suc m) = equiv-with-prop (thm2-13-1 (suc n) (suc m) ^ᵉ) (equiv-with-prop (thm2-13-1 n m) (ℕ-is-set n m))

-- * Finite sets are sets
-- For each \(n\), the type \(\operatorname{Fin}  n\) is a set.

Fin-n-is-set : (n : ℕ) → isSet (Fin n)
Fin-n-is-set zero = Empty-is-set
Fin-n-is-set (suc n) =
  coproduct-of-sets-is-set (Fin-n-is-set n) Unit-is-set


-- This extends to the dependent function too.

Fin-is-set : isSet ((n : ℕ) → Fin n)
Fin-is-set =
  fibs-are-sets-PI-is-set Fin-n-is-set
