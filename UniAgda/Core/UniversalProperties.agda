{-# OPTIONS --without-K --no-import-sorts #-}
module UniAgda.Core.UniversalProperties where

open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Functions
open import UniAgda.Core.Types.Sigma
open import UniAgda.Core.Types.Identity
open import UniAgda.Core.Types.Coproduct
open import UniAgda.Core.Types.Unit
open import UniAgda.Core.Types.Empty

open import UniAgda.Core.Homotopy
open import UniAgda.Core.Equivalences

open import UniAgda.Core.SetsAndLogic.ContrPropSet1Type
open import UniAgda.Core.SetsAndLogic.Props

open import UniAgda.Core.PathSpaces.Sigma
open import UniAgda.Core.Axioms

-- * Products
-- ** Mapping in
--  2.15.1

into-product : ∀ {i j k} {A : Type i} {B : Type j} {X : Type k}
                 → (X → A × B)
                 → (X → A) × (X → B)
into-product f = pr₁ o f , pr₂ o f


--  Theorem2.15.2

into-product-is-equiv : ∀ {i j k} {A : Type i} {B : Type j} {X : Type k}
                        → isEquiv (into-product {A = A} {B = B} {X = X})
into-product-is-equiv {A = A} {B = B} {X = X} =
  isequiv-adjointify
    ((λ { (f , g) x → (f x) , (g x)}) ,
    (λ { (f , g) → refl}) ,
    λ f → funext λ x → path-equiv-prod (refl , refl))


--  Theorem2.15.4

into-product-dep : ∀ {i j k} {X : Type i} {A : X → Type j} {B : X → Type k}
                     → ((x : X) → (A x × B x))
                     → ((x : X) → A x) × ((x : X) → B x)
into-product-dep F = (λ x → pr₁ (F x)) , (λ x → pr₂ (F x))


--  Theorem2.15.5

into-product-dep-is-equiv : ∀ {i j k} {X : Type i} {A : X → Type j} {B : X → Type k}
                            → isEquiv (into-product-dep {X = X} {A = A} {B = B})
into-product-dep-is-equiv =
  isequiv-adjointify
    ((λ { (F , G) x → F x , G x}) ,
    (λ { (F , G) → refl}) ,
    λ { F → funextD λ x → path-equiv-prod (refl , refl)})


--  2.15.6

into-dep-product : ∀ {i j k} {X : Type i} {A : X → Type j} {P : (x : X) → A x → Type k}
                     → ((x : X) → Σ[ a ∈ (A x) ] P x a)
                     → (Σ[ g ∈ ((x : X) → A x) ] ((x : X) → P x (g x)))
into-dep-product F = (λ x → pr₁ (F x)) , (λ x → pr₂ (F x))


--  Theorem2.15.7

into-dep-product-is-equiv : ∀ {i j k} {X : Type i} {A : X → Type j} {P : (x : X) → A x → Type k}
                            → isEquiv (into-dep-product {X = X} {A = A} {P = P})
into-dep-product-is-equiv =
  isequiv-adjointify
    ((λ { (F , G) x → (F x) , (G x)}) ,
    (λ { (F , G) → refl}) ,
    λ F → funextD λ x → path-equiv-sigma (refl , refl))

-- ** Mapping out

out-of-product : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
                 → (A × B → C)
                 → (A → (B → C))
out-of-product f a b = f (a , b)



out-of-product-is-equiv : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
                 → isEquiv (out-of-product {A = A} {B = B} {C = C})
out-of-product-is-equiv =
  isequiv-adjointify
  ((λ { f (a , b) → f a b}) ,
  (λ x → refl) ,
  λ x → funext λ { (a , b) → refl})



out-of-product-dep : ∀ {i j k} {A : Type i} {B : Type j} {C : A × B → Type k}
                     → ((w : A × B) → C w)
                     → ((x : A) (y : B) → C (x , y))
out-of-product-dep f a b = f (a , b)



out-of-product-dep-is-equiv : ∀ {i j k} {A : Type i} {B : Type j} {C : A × B → Type k}
                              → isEquiv (out-of-product-dep {C = C})
out-of-product-dep-is-equiv =
  isequiv-adjointify
    ((λ { F (a , b) → F a b}) ,
    (λ x → refl) ,
    λ F → funextD λ { (a , b) → refl})



out-of-dep-product : ∀ {i j k} {A : Type i} {B : A → Type j} {C : (w : Σ[ x ∈ A ] B x) → Type k}
                     → ((w : Σ A B) → C w)
                     → (x : A) (y : B x) → C (x , y)
out-of-dep-product F a b = F (a , b)


--  2.15.9

out-of-dep-product-is-equiv : ∀ {i j k} {A : Type i} {B : A → Type j} {C : (w : Σ[ x ∈ A ] B x) → Type k}
                              → isEquiv (out-of-dep-product {C = C})
out-of-dep-product-is-equiv =
  isequiv-adjointify
    ((λ {F (a , b) → F a b}) ,
    (λ x → refl) ,
    λ F → funextD λ { (a , b) → refl})

-- * Path Induction
--  2.15.10

path-induction-equiv : ∀ {i j} {A : Type i} {a : A} {B : (x : A) (p : a ≡ x) → Type j}
                       → equiv ((x : A) (p : a ≡ x) → B x p) (B a refl)
path-induction-equiv {a = a} =
  equiv-adjointify
    ((λ z → z a refl) ,
    (λ { x x₁ refl → x}) ,
    (λ x → refl) ,
    λ F → funextD λ x → funextD λ { refl → refl})

-- * Coproducts

coproduct-equiv : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
                  → equiv ((A → C) × (B → C)) (A + B → C)
coproduct-equiv =
  equiv-adjointify
    ((λ { (f , g) (inl x) → f x
        ; (f , g) (inr x) → g x}) ,
    (λ z → (λ x → z (inl x)) , (λ x → z (inr x))) ,
    (λ f → funext λ { (inl x) → refl
                    ; (inr x) → refl}) ,
    λ { (F , g) → refl})

-- * Unit

Unit-is-terminal : ∀ {i} {A : Type i}
                   → isContr (A → Unit)
Unit-is-terminal =
  (λ _ → tt) ,
  (λ f → funext λ x → Unit-is-prop tt (f x))

-- * Empty

Empty-is-initial : ∀ {i} {A : Type i}
                   → isContr (Empty → A)
Empty-is-initial =
  (λ ()) ,
  (λ f → funext λ ())

-- * Pullbacks

pullback : ∀ {i j k} {A : Type i} {B : Type j} {X : Type k}
           (f : A → X) (g : B → X)
           → Type (i ⊔ j ⊔ k)
pullback {A = A} {B = B} f g =
  Σ[ a ∈ A ] (
    Σ[ b ∈ B ] (
     (f a ≡ g b)))
