{-# OPTIONS --without-K --no-import-sorts #-}
module UniAgda.Core.SetsAndLogic.Props where

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

-- * The unit is a proposition

Unit-is-prop : isProp Unit
Unit-is-prop tt tt = refl

-- * Results
-- ** Inhabited propositions
--  Lemma3.3.2

x-in-prop-equiv-unit : {i : Level} {P : Type i}
                       → isProp P → P
                       → P ≃ Unit
x-in-prop-equiv-unit X x₀ = equiv-adjointify ((λ x → tt) , ((λ x → x₀) , ((λ { tt → refl}) , λ x → X x₀ x)))

-- ** Equivalence of propositions
-- Two propositions are equivalent if and only if they are logically
-- equivalent.
--  Lemma3.3.3

props-equiv : {i j : Level} {P : Type i} {Q : Type j}
         → isProp P → isProp Q → (P → Q) → (Q → P)
         → P ≃ Q
props-equiv {i} {j} {P} {Q} X Y f g = equiv-adjointify (f , g , ((λ y → Y ((f o g) y) y) , λ x → X ((g o f) x) x))


-- Being a proposition is preserved under equivalence.

equiv-with-prop : ∀ {i j} {A : Type i} {B : Type j}
                  → A ≃ B → isProp A
                  → isProp B
equiv-with-prop (f , g , α , β , γ) F x y = (((ap f (F (g y) (g x))) ∘ β x) ^) ∘ β y

-- ** Every proposition is a set
--  Lemma3.3.4

private
  lemma3-3-4-help : {i : Level} {A : Type i} {f : (x y : A) → x ≡ y} {x : A}
                    → (y z : A) (p : y ≡ z)
                    → (f x y) ∘ p ≡ f x z
  lemma3-3-4-help {_} {A} {f} {x} y z p = lemma2-11-2i x p (f x y) ^ ∘ apD (λ y → f x y) p

props-are-sets : {i : Level} {A : Type i}
             → isProp A → isSet A
props-are-sets {i} {A} f x y p q = pq=r-to-q=p^r (f x x) p (f x y) (lemma3-3-4-help {_} {_} {f} {x} x y p) ∘ pq=r-to-q=p^r {_} {A} {_} {_} {_} (f x x) q (f x y) (lemma3-3-4-help {_} {_} {f} {x} x y q) ^

-- ** Being a set or proposition is a proposition
--  Lemma3.3.5i

isProp-is-prop : ∀ {i}
                 (A : Type i)
                 → isProp (isProp A)
isProp-is-prop A f g =
  funextD λ x → funextD λ y → props-are-sets f x y (f x y) (g x y)

-- ** Type families with prop valued fibres
-- If a type family has prop valued fibres, then two terms are equal
-- when their first projections are equal.
--  Lemma3.5.1

fibres-props-eq : {i j : Level} {A : Type i} {P : A → Type j}
                   → ((x : A) → isProp (P x)) → (u v : Σ[ x ∈ A ] (P x)) → (pr₁ u ≡ pr₁ v)
                   → u ≡ v
fibres-props-eq {_} {_} {A} {P} X u v p = path-equiv-sigma (p , (X (pr₁ v) (transport P p (pr₂ u)) (pr₂ v)))


-- This can be extended to give an equivalence of identity types.

id-equiv-to-prop-on-type : ∀ {i j} (X X' : Type i) (Q : Type i → Type j)
              (F : (A : Type i) → isProp (Q A))
              → (a : Q X) → (b : Q X')
              → (X ≡ X') ≃ ((X , a) ≡ (X' , b))
id-equiv-to-prop-on-type X X' Q F a b = equiv-adjointify ((λ { refl → refl , (F X a b)}) ,
                         (λ { (p , u) → p}) ,
                         (λ { (refl , refl) → path-equiv-sigma (refl , (props-are-sets (F X) _ _ _ _))}) ,
                         λ { refl → refl}) oₑ (thm2-7-2 ^ᵉ)



prop-fibres-Pi-is-prop : ∀ {i j} {A : Type i} {B : A → Type j}
                         → ((x : A) → isProp (B x))
                         → isProp ((x : A) → B x)
prop-fibres-Pi-is-prop F f g = funextD λ x → F x (f x) (g x)

prop-fibres-Pi-is-prop-implicit : ∀ {i j} {A : Type i} {B : A → Type j}
                         → ((x : A) → isProp (B x))
                         → isProp ({x : A} → B x)
prop-fibres-Pi-is-prop-implicit F f g = implicit-funext λ x → F x (f {x}) (g {x})


-- This also gives us the non-dependant case.

func-of-props-is-prop : ∀ {i j} {A : Type i} {B : Type j}
                        → isProp B
                        → isProp (A → B)
func-of-props-is-prop {B = B} F f g = funext λ x → F (f x) (g x)


-- ** Propositions are preserved under products
-- Given a two proposition, their product is a proposition.

prod-of-props-is-prop : ∀ {i j} {A : Type i} {B : Type j}
                        → isProp A → isProp B
                        → isProp (A × B)
prod-of-props-is-prop H H' (a , b) (a' , b') =
  path-equiv-prod
    ((H a a') , (H' b b'))
