{-# OPTIONS --without-K --no-import-sorts #-}
module UniAgda.Core.SetsAndLogic.Contractible where

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
open import UniAgda.Core.SetsAndLogic.Props

-- * Unit is contractible

Unit-is-contr : isContr Unit
Unit-is-contr = tt , (λ { tt → refl})

-- * Equivalent definitions
--  Lemma3.11.3itoii

contr-to-pointed-prop : ∀ {i} {A : Type i}
                        → isContr A
                        → A × isProp A
contr-to-pointed-prop (a , F) = a , (λ x y → F x ^ ∘ F y)


--  Lemma3.11.3iitoi

pointed-prop-to-contr : ∀ {i} {A : Type i}
                        → A × isProp A
                        → isContr A
pointed-prop-to-contr (a , F) = a , (F a)


--  Lemma3.11.3itoiii

contr-equiv-to-Unit : ∀ {i} {A : Type i}
                      → isContr A
                      → A ≃ Unit
contr-equiv-to-Unit (a , F) = equiv-adjointify ((λ _ → tt) ,
                                               ((λ { tt → a}) ,
                                               ((λ { tt → refl}) ,
                                               λ x → F x)))


--  Lemma3.11.3iiitoi

equiv-Unit-to-contr : ∀ {i} {A : Type i}
                      → A ≃ Unit
                      → isContr A
equiv-Unit-to-contr (f , g , α , β , γ) = pointed-prop-to-contr ((g tt) , (equiv-with-prop ((f , g , α , β , γ) ^ᵉ) Unit-is-prop))

-- * Being contractible is a proposition
-- Contractible types are propositions.
--  Lemma3.11.4

contr-are-props : ∀ {i} {A : Type i}
                  → isContr A
                  → isProp A
contr-are-props X = pr₂ (contr-to-pointed-prop X)


-- Being a contractible is a proposition.
--  Corollary 3.11.5

isContr-is-prop : ∀ {i} {A : Type i}
                  → isProp (isContr A)
isContr-is-prop (a , p) (a' , p') = path-equiv-sigma ((p a') , prop-fibres-Pi-is-prop (λ x → props-are-sets (contr-are-props (a , p)) _ _) _ _)

-- * Contractibility is preserved by equivalence

equiv-with-contr : ∀ {i j} {A : Type i} {B : Type j}
                   → A ≃ B → isContr A
                   → isContr B
equiv-with-contr X Y = equiv-Unit-to-contr ((X ^ᵉ) oₑ contr-equiv-to-Unit Y)

-- * Sigma types and contractibility
--  Lemma3.11.8

Sigma-path-is-contr : ∀ {i} {A : Type i}
                      (a : A)
                      → isContr (Σ[ x ∈ A ] (a ≡ x))
Sigma-path-is-contr a = (a , refl) , (λ { (x , p) → path-equiv-sigma (p , (lemma2-11-2i a p refl))})


--  Lemma3.11.9i

lemma3-11-9i : ∀ {i j} {A : Type i} {P : A → Type j}
               → ((x : A) → isContr (P x))
               → (Σ[ x ∈ A ] P x) ≃ A
lemma3-11-9i F = equiv-adjointify ((λ x → pr₁ x) , ((λ x → x , (pr₁ (F x))) , ((λ x → refl) , (λ { (a , b) → path-equiv-sigma (refl , (contr-are-props (F a) _ _))}))))



contr-base-equiv-fibres : ∀ {i j} {A : Type i} {P : A → Type j}
                        (X : isContr A)
                        → (x : A) → (Σ[ x ∈ A ] P x) ≃ (P x)
contr-base-equiv-fibres {i} {j} {A} {P} (a , F) x = equiv-adjointify ((λ { (a' , p) → transport P (F a' ^ ∘ F x) p}) ,
                        (λ u → x , u) ,
                        ((λ u → transport (λ q → transport P q u ≡ u) (p^p (F x) ^) refl ) ,
                        λ { (a , u) → path-equiv-sigma ((F x ^ ∘ F a) , (tr-pq  (F a ^ ∘ F x) (F x ^ ∘ F a) u ^ ∘
                        transport (λ q → transport (λ v → P v) ((F a ^ ∘ F x) ∘ q) u ≡ u) (pq-^-to-q^p^ (F a ^) (F x) ∘
                        p=q-to-rp=rq (p^^=p (F a) ) (F x ^) ) (transport (λ q → (transport P q u) ≡ u) (pp^ (F a ^ ∘ F x) ^) refl) ))}))


--  Lemma3.11.9ii

lemma3-11-9ii : ∀ {i j} {A : Type i} {P : A → Type j}
                (X : isContr A)
                → (Σ[ x ∈ A ] P x) ≃ (P (pr₁ X))
lemma3-11-9ii {i} {j} {A} {P} (a , F) = contr-base-equiv-fibres (a , F) a

-- * Contractible fibres
--  Lemma3.11.6

contr-fibres-to-contr-Pi : ∀ {i j} {A : Type i} {P : A → Type j}
                           → ((x : A) → isContr (P x))
                           → isContr ((x : A) → P x)
contr-fibres-to-contr-Pi F = pointed-prop-to-contr ((λ x → pr₁ (F x)) , (prop-fibres-Pi-is-prop (λ x → contr-are-props (F x))))



contr-fibres-to-contr-Sigma : ∀ {i j} {A : Type i} {P : A → Type j}
                              → ((x : A) → isContr (P x)) → (isContr A)
                              → isContr (Σ[ x ∈ A ] P x)
contr-fibres-to-contr-Sigma F X = equiv-with-contr (lemma3-11-9i F ^ᵉ) X

-- * Path spaces
-- Contractible types have contractible path spaces.

contr-has-contr-path-space : ∀ {i} {A : Type i} {x y : A}
                             → isContr A → isContr (x ≡ y)
contr-has-contr-path-space {i} {A} {x} {y} (a , F) = (F x) ^ ∘ F y , λ { refl → p^p (F x)}
