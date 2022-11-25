
{-# OPTIONS --without-K --rewriting --no-import-sorts #-}
module UniAgda.Equiv.Inj-Surj where

open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Functions
open import UniAgda.Core.Types.Identity
open import UniAgda.Core.Types.Sigma

open import UniAgda.Core.PathAlgebra
open import UniAgda.Core.Homotopy

open import UniAgda.Core.Axioms
open import UniAgda.Core.Equivalences

open import UniAgda.Core.SetsAndLogic.ContrPropSet1Type
open import UniAgda.Core.SetsAndLogic.Props
open import UniAgda.Core.SetsAndLogic.Contractible
open import UniAgda.Core.SetsAndLogic.Equivalences

open import UniAgda.Core.PathSpaces.Sigma
open import UniAgda.Core.PathSpaces.Identity

open import UniAgda.HITs.PropTrunc

-- * Results

isSurjective : ∀ {i j} {A : Type i} {B : Type j}
       (f : A → B)
       → Type (i ⊔ j)
isSurjective {i} {j} {A} {B} f = (b : B) → ∥ fib f b ∥ 

isSurjective-is-prop : ∀ {i j} {A : Type i} {B : Type j}
                     (f : A → B)
                     → isProp (isSurjective f)
isSurjective-is-prop f =
  prop-fibres-Pi-is-prop
    λ b → prop-trunc-is-prop (fib f b)



isEmbedding : ∀ {i j} {A : Type i} {B : Type j}
          (f : A → B)
          → Type (i ⊔ j)
isEmbedding {i} {j} {A} {B} f = (x y : A) → isEquiv (ap {i} {j} {A} {B} {x} {y} f)

isEmbedding-is-prop : ∀ {i j} {A : Type i} {B : Type j}
          (f : A → B)
          → isProp (isEmbedding f)
isEmbedding-is-prop f =
  prop-fibres-Pi-is-prop λ a →
    prop-fibres-Pi-is-prop λ b →
      isEquiv-is-prop (ap f)

isInjective : ∀ {i j} {A : Set_ i} {B : Set_ j}
            (f : pr₁ A → pr₁ B)
            → Type (i ⊔ j)
isInjective {i} {j} {A , p} {B , q} f = (x y : A) → (f x ≡ f y) → (x ≡ y)

isInjective-is-prop : ∀ {i j} {A : Set_ i} {B : Set_ j}
                    (f : pr₁ A → pr₁ B)
                    → isProp (isInjective {A = A} {B = B} f)
isInjective-is-prop {i} {j} {A , X} {B , Y} f =
  prop-fibres-Pi-is-prop λ x →
    prop-fibres-Pi-is-prop λ y →
      func-of-props-is-prop (X x y)


thm4-6-3 : ∀ {i j} {A : Type i} {B : Type j} {f : A → B}
           → isEquiv f ↔ (isSurjective f × isEmbedding f)
thm4-6-3 {i} {j} {A} {B} {f} =
         (λ x → (λ b → ∣ pr₁ (isEquiv-to-isContrmap x b) ∣) , λ a b → thm2-11-1 x) ,
         λ { (X , Y) → isContrmap-to-isEquiv λ y →
           pointed-prop-to-contr
             (pr₁ (pr₂ (lemma3-9-1  λ { (a , p) (a₁ , q) →
               path-equiv-sigma ((pr₁ (Y a a₁) (p ∘ (q ^))) ,
                 tr-Pf (λ x → x ≡ y) f (pr₁ (Y a a₁) (p ∘ q ^)) p ∘
                 lemma2-11-2ii y (ap f (pr₁ (Y a a₁) (p ∘ q ^) )) p ∘
                 p=qr-to-q^p=r p q _ (pq^=r-to-p=rq p q _
                   (pr₁ (pr₂ (pr₂ (Y a a₁))) (p ∘ q ^) ^)) )}))
             (X y) ,
             λ { (a , p) (a₁ , q) → path-equiv-sigma ((pr₁ (Y a a₁) (p ∘ (q ^))) ,
               tr-Pf (λ x → x ≡ y) f (pr₁ (Y a a₁) (p ∘ q ^)) p ∘
               lemma2-11-2ii y (ap f ( pr₁ (Y a a₁) (p ∘ q ^) )) p ∘
               p=qr-to-q^p=r p q _
                 (pq^=r-to-p=rq p q _
                   (pr₁ (pr₂ (pr₂ (Y a a₁))) (p ∘ q ^) ^)) )})}


cor4-6-4 : ∀ {i j} {A : Type i} {B : Type j}
           (f : A → B)
           → isEquiv f ≃ (isSurjective f × isEmbedding f)
cor4-6-4 f =
  props-equiv
    (isEquiv-is-prop f)
    (prod-of-props-is-prop
      (isSurjective-is-prop f)
      (isEmbedding-is-prop f))
    (pr₁ (thm4-6-3 {f = f}))
    (pr₂ (thm4-6-3 {f = f}))
