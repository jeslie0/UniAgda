{-# OPTIONS --without-K  --no-import-sorts #-}
module UniAgda.Categories.Natural-Transformation where


open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Functions
open import UniAgda.Core.Types.Identity
open import UniAgda.Core.Types.Sigma

open import UniAgda.Core.SetsAndLogic.ContrPropSet1Type
open import UniAgda.Core.SetsAndLogic.Props
open import UniAgda.Core.SetsAndLogic.Sets

open import UniAgda.Core.Equivalences

open import UniAgda.Core.PathSpaces.Sigma

open import UniAgda.Core.Axioms

open import UniAgda.Categories.Category
open import UniAgda.Categories.Functor

open Precategory
open Functor

-- * Natural transformations
-- A natural transformation is a map between functors. We define it as
-- a record.

record NaturalTransformation {i j k l : Level} {A : Precategory i j} {B : Precategory k l} (F G : Functor A B) : Type (i ⊔ j ⊔ l) where
  eta-equality
  field
    α-ob : (x : A .ob) → B .hom (F .F₀ x) (G .F₀ x)
    α-nat : {x y : A .ob} (f : A [ x , y ]) → (α-ob y) o⟨ B ⟩ (F .F₁ f) ≡ (G .F₁ f) o⟨ B ⟩ (α-ob x)

  open Functor


-- As precategories have sets of morphisms, the hom condition is a
-- proposition. We use this later to show that there is a set of
-- natural transformations between two functors.

  α-hom-is-prop : {x y : A .ob}
                  → isProp ((f : hom A x y) → comp B (α-ob y) (F .F₁ f) ≡ comp B (G .F₁ f) (α-ob x))
  α-hom-is-prop = prop-fibres-Pi-is-prop λ f₁ → sets-have-prop-ids _ (B .hom-set _ _) _ _


-- ** Sigma definition and equivalence
-- The Σ definition of a natural transformation is presented here.

Nat-trans-sig : {i j k l : Level} {A : Precategory i j} {B : Precategory k l}
            (F G : Functor A B)
            → Type (i ⊔ j ⊔ l)
Nat-trans-sig {i} {j} {k} {l} {A} {B} F G =
  let module A = Precategory A in
  let module B = Precategory B in
  let module F = Functor F in
  let module G = Functor G in
    Σ[ α-ob ∈ ((x : A.ob) → B.hom (F.₀ x) (G.₀ x)) ] (
    {x y : A.ob} (f : A.hom x y) → B.comp (α-ob y) (F.₁ f) ≡ B.comp (G.₁ f) (α-ob x))


-- Of course, we have an equivalence between the two definitions.

nat-trans-sig→rec : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l}
                     (F G : Functor A B)
                     → Nat-trans-sig F G → NaturalTransformation F G
NaturalTransformation.α-ob (nat-trans-sig→rec F G (α₁ , α₂)) = α₁
NaturalTransformation.α-nat (nat-trans-sig→rec F G (α₁ , α₂)) = α₂

nat-trans-rec→sig : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l}
                       (F G : Functor A B)
                       → NaturalTransformation F G → Nat-trans-sig F G
nat-trans-rec→sig F G record { α-ob = α-ob ; α-nat = α-nat } =
  α-ob ,
  α-nat

nat-trans-rec→sig→rec : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l}
                 (F G : Functor A B)
                 → (α : NaturalTransformation F G) → (nat-trans-sig→rec F G o nat-trans-rec→sig F G) α ≡ α
nat-trans-rec→sig→rec F G α = refl

nat-trans-sig→rec→sig : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l}
                 (F G : Functor A B)
                 → (α : Nat-trans-sig F G) → (nat-trans-rec→sig F G o nat-trans-sig→rec F G) α ≡ α
nat-trans-sig→rec→sig F G (a , b) = path-equiv-sigma
  (refl , refl)

Nat-trans-sig-equiv : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l}
               (F G : Functor A B)
               → (Nat-trans-sig F G) ≃ (NaturalTransformation F G)
Nat-trans-sig-equiv F G = equiv-adjointify
  (nat-trans-sig→rec F G ,
  (nat-trans-rec→sig F G) ,
  (nat-trans-rec→sig→rec F G) ,
  (nat-trans-sig→rec→sig F G))



open NaturalTransformation


-- * Natural transformations properties
-- As natural transformations have a prop as their second piece of
-- data, we only need to consider what two natural transformations do
-- on objects, to see if they are equal or not.

nat-trans-id : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l}
               {F G : Functor A B} {α β : NaturalTransformation F G}
               → (α .α-ob ≡ β .α-ob) → α ≡ β
nat-trans-id {i} {j} {k} {l} {A} {B} {F} {G} {α} {β} p =
  equiv-types-eq (Nat-trans-sig-equiv F G)
    (fibres-props-eq
      (λ T X Y → implicit-funext λ a →
        implicit-funext λ b →
          funextD λ f → B .hom-set _ _ _ _ (X f) (Y f))
      ((α .α-ob) , (α .α-nat))
      ((β .α-ob) , (β .α-nat))
      p)


-- As previously mentioned, the type of natural transformations between two functors is a set.

Nat-trans-is-set : {i j k l : Level} {A : Precategory i j} {B : Precategory k l}
                      (F G : Functor A B)
                      → isSet (NaturalTransformation F G)
Nat-trans-is-set {A = A} {B = B} F G = equiv-with-set (Nat-trans-sig-equiv F G)
  (prop-fibres-totalspace-set
    (fibs-are-sets-PI-is-set (λ x → B .hom-set (F .F₀ x) (G . F₀ x)))
    λ a P Q → implicit-funext
      λ x → implicit-funext
      λ y → funextD λ f → sets-have-prop-ids _ (B .hom-set (F .F₀ x) (G . F₀ y)) _ _ (P f) (Q f))


-- * Categorical properties
-- We prove some useful results which will be used to show that
-- functors form a precategory. Firstly, there is an identity natural
-- transformation.

idⁿ : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l} {F : Functor A B}
      → NaturalTransformation F F
idⁿ {i} {j} {k} {l} {A} {B} {F} =
  record { α-ob = λ x → B .Id ;
           α-nat = λ f → B .IdR (F .F₁ f) ∘ B .IdL (F .F₁ f) ^ }


-- We also have (vertical) composition of natural transformations.

nat-trans-compᵛ : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l} {F G H : Functor A B}
                  (β : NaturalTransformation G H) (α : NaturalTransformation F G)
                  → NaturalTransformation F H
nat-trans-compᵛ {i} {j} {k} {l} {A} {B} {F} {G} {H}
  record { α-ob = β₁ ; α-nat = β₂ }
  record { α-ob = α₁ ; α-nat = α₂ } =
    record { α-ob = (λ a → (β₁ a) o⟨ B ⟩ (α₁ a)) ;
             α-nat = λ { {x} {y} f → B .Assoc (F .F₁ f) (α₁ y) (β₁ y) ^ ∘
               precat-whiskerL B (α₂ f) (β₁ y) ∘
               B .Assoc (α₁ x) (G .F₁ f) (β₁ y) ∘
               precat-whiskerR B (β₂ f) (α₁ x) ∘
               B .Assoc (α₁ x) (β₁ x) (H .F₁ f) ^} }

_oᴺ_ = nat-trans-compᵛ
infixr 9 _oᴺ_


-- Composing with the identity is as expected.

nat-trans-id-compᵛ : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l} {F G : Functor A B}
                     (α : NaturalTransformation F G)
                     → nat-trans-compᵛ idⁿ α ≡ α
nat-trans-id-compᵛ {B = B} record { α-ob = α₁ ; α-nat = α₂ } =
  nat-trans-id (funextD λ x → B .IdR (α₁ x))


nat-trans-compᵛ-id : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l} {F G : Functor A B} (α : NaturalTransformation F G)
                     → nat-trans-compᵛ  α idⁿ ≡ α
nat-trans-compᵛ-id {B = B} record { α-ob = α₁ ; α-nat = α₂ } =
  nat-trans-id (funextD λ x → B .IdL (α₁ x))


-- Finally, composition is associative.

nat-trans-comp-assoc : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l} {F G H K : Functor A B}
                       (α : NaturalTransformation F G) (β : NaturalTransformation G H) (γ : NaturalTransformation H K)
                     → nat-trans-compᵛ γ (nat-trans-compᵛ β α) ≡ nat-trans-compᵛ (nat-trans-compᵛ γ β) α
nat-trans-comp-assoc {B = B}
  record { α-ob = α₁ ; α-nat = α₂ }
  record { α-ob = β₁ ; α-nat = β₂ }
  record { α-ob = γ₁ ; α-nat = γ₂ } =
         nat-trans-id
      (funextD λ x → B .Assoc (α₁ x) (β₁ x) (γ₁ x))


-- ** 2 - Categorical aspects
-- Natural transformations also have a notion of horizontal composition.

-- compʰ : ∀ {i₁ i₂ i₃ i₄ i₅ i₆} {A : Precategory i₁ i₂} {B : Precategory i₃ i₄} {C : Precategory i₅ i₆} {F F' : Functor A B} {G G' : Functor B C}
--           (β : NaturalTransformation G G') (α : NaturalTransformation F F')
--           → NaturalTransformation (compᶠ G F) (compᶠ G' F')
-- α-ob (compʰ {C = C} {F = F} {G' = G'} β α) a = comp C (G' .F₁ (α .α-ob a)) (β .α-ob (F .F₀ a))
-- α-nat (compʰ β α) f = {!!}


-- We can also whisker natural transformations with functors.

-- _▹_ : ∀ {i₁ i₂ i₃ i₄ i₅ i₆} {A : Precategory i₁ i₂} {B : Precategory i₃ i₄} {C : Precategory i₅ i₆} {G H : Functor B C}
--         (γ : NaturalTransformation G H) (F : Functor A B)
--         → NaturalTransformation (compᶠ G F) (compᶠ H F)
-- α-ob (γ ▹ F) a = γ .α-ob (F .F₀ a)
-- α-nat (γ ▹ F) f = γ .α-nat (F .F₁ f)

-- _◃_ : ∀ {i₁ i₂ i₃ i₄ i₅ i₆} {A : Precategory i₁ i₂} {B : Precategory i₃ i₄} {C : Precategory i₅ i₆} {G H : Functor A B}
--       (F : Functor B C) (γ : NaturalTransformation G H) 
--       → NaturalTransformation (compᶠ F G) (compᶠ F H)
-- α-ob (F ◃ γ) a = F .F₁ (γ .α-ob a)
-- α-nat (_◃_ {G = G} {H = H} F γ) {x} {y} f =
--   F .F-comp (γ .α-ob y) (G .F₁ f) ^ ∘
--   ap (λ z → F₁ F z) (γ .α-nat f) ∘
--   F .F-comp (H .F₁ f) (γ .α-ob x)
