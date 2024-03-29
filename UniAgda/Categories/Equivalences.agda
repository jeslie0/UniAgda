{-# OPTIONS --without-K --rewriting --no-import-sorts #-}
module UniAgda.Categories.Equivalences where

open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Functions
open import UniAgda.Core.Types.Identity
open import UniAgda.Core.Types.Sigma

open import UniAgda.Core.SetsAndLogic.ContrPropSet1Type
open import UniAgda.Core.SetsAndLogic.Props

open import UniAgda.Core.PathSpaces.Sigma

open import UniAgda.Core.Axioms

open import UniAgda.Equiv.Inj-Surj
open import UniAgda.Logic.Exists

open import UniAgda.Core.Equivalences

open import UniAgda.HITs.PropTrunc

open import UniAgda.Categories.Category
open import UniAgda.Categories.Functor
open import UniAgda.Categories.Natural-Transformation
open import UniAgda.Categories.Adjunctions


-- * Definition

record isCatEquiv {i j k l : Level} {A : Precategory i j} {B : Precategory k l}
       (F : Functor A B)
       : Type (i ⊔ j ⊔ k ⊔ l) where
  eta-equality
  module A = Precategory A
  module B = Precategory B
  module F = Functor F
  field
    adj : isLeftAdjoint F

  module adj = isLeftAdjoint adj

  field
    unit-is-iso : (a : A.ob) → A.isIso (adj.unit.α-ob a)
    counit-is-iso : (b : B.ob) → B.isIso (adj.counit.α-ob b)

-- ** Sigma version

isCatEquiv-sig : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l}
                 (F : Functor A B)
                 → Type (i ⊔ j ⊔ k ⊔ l)
isCatEquiv-sig {A = A} {B = B} F =
  Σ[ adj ∈ (isLeftAdjoint F) ] (
    let module F = Functor F in
    let module A = Precategory A in
    let module B = Precategory B in
    let module adj = isLeftAdjoint adj in
    Σ[ unit-is-iso ∈ ((a : A.ob) → A.isIso (adj.unit.α-ob a)) ] (
      (b : B.ob) → B.isIso (adj.counit.α-ob b)))

isCatEquiv-sig→rec : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l} {F : Functor A B}
                     → isCatEquiv-sig F → isCatEquiv F
isCatEquiv.adj (isCatEquiv-sig→rec eqv) = pr₁ eqv
isCatEquiv.unit-is-iso (isCatEquiv-sig→rec eqv) = pr₁ (pr₂ eqv)
isCatEquiv.counit-is-iso (isCatEquiv-sig→rec eqv) = pr₂ (pr₂ eqv)

isCatEquiv-rec→sig : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l} {F : Functor A B}
                     → isCatEquiv F → isCatEquiv-sig F
isCatEquiv-rec→sig eqv =
  let module eqv = isCatEquiv eqv in
  eqv.adj ,
  eqv.unit-is-iso ,
  eqv.counit-is-iso

isCatEquiv-rec→sig→rec : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l} {F : Functor A B}
                         (eqv : isCatEquiv F)
                         → (isCatEquiv-sig→rec {i} {j} {k} {l} {A} {B} {F} o isCatEquiv-rec→sig) eqv ≡ eqv
isCatEquiv-rec→sig→rec eqv = refl

isCatEquiv-sig→rec→sig : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l} {F : Functor A B}
                         (eqv : isCatEquiv-sig F)
                         → (isCatEquiv-rec→sig o isCatEquiv-sig→rec) eqv ≡ eqv
isCatEquiv-sig→rec→sig eqv =
  path-equiv-sigma (refl ,
    (path-equiv-sigma (refl ,
      refl)))

isCatEquiv-sig-Equiv : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l} {F : Functor A B}
                       → isCatEquiv-sig F ≃ isCatEquiv F
isCatEquiv-sig-Equiv = equiv-adjointify
  (isCatEquiv-sig→rec ,
  isCatEquiv-rec→sig ,
  isCatEquiv-rec→sig→rec ,
  isCatEquiv-sig→rec→sig)

-- ** Natural transformation version
-- In category theory, one usually defines an equivalence of
-- categories by giving two functors which are pseudo-inverses. This
-- is a result in our setup.
-- Lemma9.4.2




-- ** Fully faithful, essentially surjective

--  Definition9.4.3

isFaithful : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l}
           (F : Functor A B)
           → Type (i ⊔ j ⊔ l)
isFaithful {A = A} {B = B} F = (a b : Precategory.ob A) → isInjective {A = (A [ a , b ]) , (Precategory.hom-set A a b)} {B = (B [ Functor.F₀ F a , Functor.F₀ F b ]) , Precategory.hom-set B (Functor.F₀ F a) (Functor.F₀ F b)} (Functor.F₁ F {a = a} {b = b})

isFaithful-is-prop : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l}
                     (F : Functor A B)
                     → isProp (isFaithful F)
isFaithful-is-prop {A = A} {B = B} F =
  let module A = Precategory A
      module B = Precategory B
      module F = Functor F in
  prop-fibres-Pi-is-prop λ x →
    prop-fibres-Pi-is-prop λ y →
      isInjective-is-prop
        {A = (A.hom x y , A.hom-set x y)}
        {B = (B.hom (F.₀ x) (F.₀ y) , B.hom-set (F.₀ x) (F.₀ y))}
        F.₁

isFull : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l}
       (F : Functor A B)
       → Type (i ⊔ j ⊔ l)
isFull {A = A} {B = B} F = (a b : Precategory.ob A) → isSurjective (Functor.F₁ F {a} {b})

isFull-is-prop : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l}
                 (F : Functor A B)
                 → isProp (isFull F)
isFull-is-prop F =
  prop-fibres-Pi-is-prop λ x →
    prop-fibres-Pi-is-prop λ y →
      isSurjective-is-prop (Functor.F₁ F)

isFullyFaithful : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l}
                 (F : Functor A B)
                 → Type (i ⊔ j ⊔ l)
isFullyFaithful {A = A} {B = B} F = isFull F × isFaithful F

isFullyFaithful-is-prop : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l}
                          (F : Functor A B)
                          → isProp (isFullyFaithful F)
isFullyFaithful-is-prop F =
  prod-of-props-is-prop
    (isFull-is-prop F)
    (isFaithful-is-prop F)


--  Definition9.4.4

split-essentially-surjective : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l}
                               (F : Functor A B)
                               → Type (i ⊔ k ⊔ l)
split-essentially-surjective {A = A} {B = B} F =
  (b : Precategory.ob B) →
    Σ[ a ∈ (Precategory.ob A) ] (
      Precategory.iso B (Functor.F₀ F a) b)


-- We aim to show that a equivalences fully faithful, split
--  essentially surjective functions are equivalent as types.
--  Lemma9.4.5




-- As we are working constructively, essentially surjective by itself
--  means that there merely exists an isomorphism, whilst split
--  essentially surjective gives us a specific choice. We define the
--  former here.
--  Definition9.4.6i

isEssentiallySurjective : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l}
                         (F : Functor A B)
                         → Type (i ⊔ k ⊔ l)
isEssentiallySurjective {A = A} {B = B} F =
  (b : Precategory.ob B) →
    ∃[ a ∈ (Precategory.ob A) ] (
      Precategory.iso B (Functor.F₀ F a) b)

isEssentiallySurjective-is-prop : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l}
                                  (F : Functor A B)
                                  → isProp (isEssentiallySurjective F)
isEssentiallySurjective-is-prop F =
  prop-fibres-Pi-is-prop λ b →
    prop-trunc-is-prop _


-- This leads us to the notion of a weak equivalence between
--  categories.
--  Definition9.4.6ii

isWeakEquivalence : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l}
                   (F : Functor A B)
                   → Type (i ⊔ j ⊔ k ⊔ l)
isWeakEquivalence F = isFull F × isFaithful F × isEssentiallySurjective F


-- Being a weak equivalence is a proposition.

isWeakEquivalence-is-prop : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l}
                            (F : Functor A B)
                            → isProp (isWeakEquivalence F)
isWeakEquivalence-is-prop {A = A} F =
  prod-of-props-is-prop
    (isFull-is-prop F)
    (prod-of-props-is-prop
      (isFaithful-is-prop F)
      (isEssentiallySurjective-is-prop F))
