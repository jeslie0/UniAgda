{-# OPTIONS --without-K --rewriting --no-import-sorts #-}
module UniAgda.Categories.Examples.FiniteSets where

open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Sigma
open import UniAgda.Core.Types.Identity
open import UniAgda.Core.Types.Nat
open import UniAgda.Core.Types.Functions
open import UniAgda.Core.Types.FiniteSets

open import UniAgda.Core.Equivalences

open import UniAgda.Core.SetsAndLogic.ContrPropSet1Type
open import UniAgda.Core.SetsAndLogic.Sets

open import UniAgda.HITs.PropTrunc

open import UniAgda.Categories.Category

-- * The type of finite sets
-- Following
-- [[https://homotopytypetheory.org/2016/07/20/combinatorial-species-and-finite-sets-in-hott/][this
-- blog post]], we define the property of some type \(A\) being finite
-- as the propositional truncation of there existing some \(n\) such
-- that \(A \simeq \operatorname{Fin} n\).

isFinite : ∀ {i}
           (A : Type i)
           → Type i
isFinite A = Σ[ n ∈ ℕ ] ∥ (A ≃ Fin n) ∥


-- We then define the type of finite sets to be the appropriate
-- \(\Sigma\)-type.

Fin-set : ∀ (i)
          → Type (lsuc i)
Fin-set i = Σ[ A ∈ (Type i) ] isFinite A


If a type \(A\) is a finite set, then it is indeed a set.

finite-sets-are-sets : ∀ {i} (A : Fin-set i)
                       → isSet (pr₁ A)
finite-sets-are-sets (A , n , b) =
  prop-trunc-rec
    (isSet-is-prop A)
    (λ x → equiv-with-set (x ^ᵉ) (Fin-n-is-set n))
    b

-- * The precategory of finite sets

FIN-SET : (i : Level) → Precategory (lsuc i) i
Precategory.ob (FIN-SET i) = Σ[ A ∈ (Type i) ] isFinite A
Precategory.hom (FIN-SET i) (A , X) (B , Y) = A → B
Precategory.hom-set (FIN-SET i) (A , X) (B , Y) = func-of-sets-is-set (finite-sets-are-sets (B , Y)) 
Precategory.Id (FIN-SET i) {a = (A , X)} = id
Precategory.comp (FIN-SET i) {a , b} {a₁ , b₁} {a₂ , b₂} g f = g o f
Precategory.IdL (FIN-SET i) {a , b} {a₁ , b₁} f = refl
Precategory.IdR (FIN-SET i) {a , b} {a₁ , b₁} f = refl
Precategory.Assoc (FIN-SET i) {a , b} {a₁ , b₁} {a₂ , b₂} {a₃ , b₃} f g h = refl
