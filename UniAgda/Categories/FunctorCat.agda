{-# OPTIONS --without-K  --no-import-sorts #-}
module UniAgda.Categories.FunctorCat where

open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Functions
open import UniAgda.Core.Types.Identity
open import UniAgda.Core.Types.Sigma

open import UniAgda.Categories.Category
open import UniAgda.Categories.Functor
open import UniAgda.Categories.Natural-Transformation

open import UniAgda.Core.PathSpaces.Sigma

open import UniAgda.Core.Axioms

open Precategory
open Category
open Functor
open NaturalTransformation

-- * Functor Precategories
-- Given two precategories, there is a precategory of functors between them, with natural transformations as morphisms.

_^_ : ∀ {i₁ i₂ i₃ i₄} (A : Precategory i₁ i₂) (B : Precategory i₃ i₄)
      → Precategory (i₁ ⊔ i₂ ⊔ i₃ ⊔ i₄) (i₂ ⊔ i₃ ⊔ i₄)
ob (A ^ B) = Functor B A
hom (A ^ B) F G = NaturalTransformation F G
hom-set (A ^ B) = Nat-trans-is-set
Id (A ^ B) = idⁿ
comp (A ^ B) = nat-trans-compᵛ
IdL (A ^ B) = nat-trans-compᵛ-id
IdR (A ^ B) = nat-trans-id-compᵛ
Assoc (A ^ B) = nat-trans-comp-assoc

-- * Natural isomorphisms
-- One of the first results about natural transformations that one proves, is that a natural transformation is an isomorphism if and only if each component is an isomorphism. We prove that now, hiding each direction in a "private" environment. The forward direction is straightforward, we just need to convert the paths between records into a path between Σ types. Then it is easy to show that we do have an isomorphism.

private
  lemma9-2-4i : ∀ {i₁ i₂ i₃ i₄} {A : Precategory i₁ i₂} {B : Precategory i₃ i₄} {F G : (B ^ A) .ob}
                  (γ : (B ^ A) .hom F G)
                  → isIso (B ^ A) γ → ((a : A .ob) → isIso B (γ .α-ob a))
  lemma9-2-4i {B = B} {F = F} {G = G} γ (α , p , q) a =
    let q' = ap (nat-trans-rec→sig F F) q
        p' = ap (nat-trans-rec→sig G G) p in
    (α .α-ob a) ,
    happlyD (pr₁ (path-sigma p')) a ,
    happlyD (pr₁ (path-sigma q')) a


-- The reverse direction mainly consists of some path algebra. It is mathematically straightforward, but due to associativity, can be unsightly in the details.

  lemma9-2-4ii : ∀ {i₁ i₂ i₃ i₄} {A : Precategory i₁ i₂} {B : Precategory i₃ i₄} {F G : (B ^ A) .ob}
                  (γ : (B ^ A) .hom F G)
                   → ((a : A .ob) → isIso B (γ .α-ob a)) → isIso (B ^ A) γ
  lemma9-2-4ii {B = B} {F = F} {G = G} record { α-ob = γ₁ ; α-nat = γ₂ } δ =
    record { α-ob = λ a → pr₁ (δ a) ;
             α-nat = λ { {a} {b} f →
               (((((((IdL B (pr₁ (δ b) o⟨ B ⟩ G .F₁ f) ^
                 ∘ precat-whiskerL B (pr₁ (pr₂ (δ a)) ^) (pr₁ (δ b) o⟨ B ⟩ G .F₁ f))
                 ∘ Assoc B (pr₁ (δ a)) (γ₁ a) (pr₁ (δ b) o⟨ B ⟩ G .F₁ f))
                 ∘ precat-whiskerR B (Assoc B (γ₁ a) (G .F₁ f) (pr₁ (δ b)) ^) (pr₁ (δ a)))
                 ∘ precat-whiskerR B (precat-whiskerL B (γ₂ f ^) (pr₁ (δ b))) (pr₁ (δ a)))
                 ∘ precat-whiskerR B (Assoc B (F .F₁ f) (γ₁ b) (pr₁ (δ b)) ) (pr₁ (δ a)))
                 ∘ (Assoc B (pr₁ (δ a)) (F .F₁ f) ((pr₁ (δ b)) o⟨ B ⟩ (γ₁ b)) ^))
               ∘ ap (λ Z → comp B (Z) (comp' B (F .F₁ f) (pr₁ (δ a)))) (pr₂ (pr₂ (δ b))))
               ∘ IdR B (F .F₁ f o⟨ B ⟩ pr₁ (δ a))} } ,
    (nat-trans-id (funextD λ x → pr₁ (pr₂ (δ x)))) ,
    (nat-trans-id (funextD λ x → pr₂ (pr₂ (δ x))))


-- Combining the above results, we get the desired proof.

nat-trans-iso-components : ∀ {i₁ i₂ i₃ i₄} {A : Precategory i₁ i₂} {B : Precategory i₃ i₄} {F G : (B ^ A) .ob}
                             (γ : (B ^ A) .hom F G)
                             → isIso (B ^ A) γ ↔ ((a : A .ob) → isIso B (γ .α-ob a))
nat-trans-iso-components γ =
  (lemma9-2-4i γ) ,
  (lemma9-2-4ii γ)

-- * Functor Categories
-- A result which will be central to the study of categories is the
-- following: if A is a precategory and B is a category, then B ^ A is
-- also a category. We need to show that id-to-iso in B ^ A is an
-- equivalence, so first, we define a quasi-inverse to it.

-- private
--   functor-cat-γ' : ∀ {i₁ i₂ i₃ i₄} {A : Precategory i₁ i₂} {B : Precategory i₃ i₄}
--                      (univB : isCategory B) (F G : (B ^ A) .ob)
--                      → iso (B ^ A) F G → F ≡ G
--   functor-cat-γ' univB F G (α , αIsIso) =
--     let αIsoComponents = lemma9-2-4i α αIsIso
--     in Functor-path
--     (funext (λ a → (pr₁ $ univB (F₀ F a) (F₀ G a)) ((α-ob α a) , (αIsoComponents a)) ))
--     {!!}


-- functor-cat-condition : ∀ {i₁ i₂ i₃ i₄} {A : Precategory i₁ i₂} {B : Precategory i₃ i₄}
--                         → isCategory B
--                         → isCategory (B ^ A)
-- functor-cat-condition {A = A} {B = B} univB F G =
--   isequiv-adjointify
--     ((λ { γ → Functor-path
--         (funext (λ a → pr₁ (univB (F .F₀ a) (G .F₀ a)) (((pr₁ γ) .α-ob a ) , (lemma9-2-4i (pr₁ γ) (pr₂ γ) a))) )
--         {!!}}) ,
--     (λ { (γ , γiso) → fibres-props-eq (isIso-is-prop (B ^ A)) _ _
--        (nat-trans-id (funextD λ a → {!re!}))}) ,
--     λ x → {!!})
