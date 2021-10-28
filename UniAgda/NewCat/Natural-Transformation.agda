{-# OPTIONS --without-K  --no-import-sorts #-}
module Natural-Transformation where


open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Functions
open import UniAgda.Core.Types.Identity
open import UniAgda.Core.Types.Sigma

open import UniAgda.Core.SetsAndLogic.ContrPropSet1Type
open import UniAgda.Core.SetsAndLogic.Props
open import UniAgda.Core.SetsAndLogic.Sets

open import UniAgda.Core.Homotopy

open import UniAgda.Core.Equivalences

open import UniAgda.Core.PathSpaces.Sigma

open import UniAgda.Core.Axioms

open import Category
open import Functor

open Precategory
open Functor.Functor

private
  variable
    i₁ i₂ i₃ i₄ : Level

-- | Natural transformation definition
record NaturalTransformation {i₁ i₂ i₃ i₄ : Level} {A : Precategory i₁ i₂} {B : Precategory i₃ i₄}
                             (F G : Functor A B) : Type (i₁ ⊔ i₂ ⊔ i₄) where
  eta-equality
  field
    α-ob : (x : Ob A) → B [ F₀ F x , F₀ G x ]
    α-nat : {x y : Ob A} (f : A [ x , y ]) → (α-ob y) o⟨ B ⟩ (F₁ F f) ≡ (F₁ G f) o⟨ B ⟩ (α-ob x)

open NaturalTransformation


module NaturalTransformation-Σ-Equivalence where
  private
    variable
      A : Precategory i₁ i₂
      B : Precategory i₃ i₄
      F G : Functor A B

  NaturalTransformation-sig : {i₁ i₂ i₃ i₄ : Level} {A : Precategory i₁ i₂} {B : Precategory i₃ i₄}
                             (F G : Functor A B)
                             → Type (i₁ ⊔ i₂ ⊔ i₄)
  NaturalTransformation-sig {A = A} {B = B} F G =
    Σ[ α-ob ∈ ((x : Ob A) → B [ F₀ F x , F₀ G x ]) ]
      ({x y : Ob A} (f : A [ x , y ]) → (α-ob y) o⟨ B ⟩ (F₁ F f) ≡ (F₁ G f) o⟨ B ⟩ (α-ob x))

  naturaltransformation-sig→rec : (F G : Functor A B)
                                  → NaturalTransformation-sig F G
                                  → NaturalTransformation F G
  naturaltransformation-sig→rec F G (α-ob , α-nat) = record { α-ob = α-ob
                                                        ; α-nat = α-nat
                                                        }

  naturaltransformation-rec→sig : (F G : Functor A B)
                                  → NaturalTransformation F G
                                  → NaturalTransformation-sig F G
  naturaltransformation-rec→sig F G x = (α-ob x) , (α-nat x)

  naturaltransformation-rec→sig→rec : (F G : Functor A B)
                                    → (naturaltransformation-sig→rec F G o naturaltransformation-rec→sig F G) ~ id
  naturaltransformation-rec→sig→rec F G x = refl

  naturaltransformation-sig→rec→sig : (F G : Functor A B)
                                      → (naturaltransformation-rec→sig F G o naturaltransformation-sig→rec F G) ~ id
  naturaltransformation-sig→rec→sig F G (α , β) = refl

  NaturalTransformation-sig-Equiv : {F G : Functor A B}
                                    → NaturalTransformation-sig F G ≃ NaturalTransformation F G
  NaturalTransformation-sig-Equiv {F = F} {G = G} =
    equiv-adjointify
      ( naturaltransformation-sig→rec F G
      , naturaltransformation-rec→sig F G
      , naturaltransformation-rec→sig→rec F G
      , naturaltransformation-sig→rec→sig F G)


open NaturalTransformation-Σ-Equivalence

NaturalTransformation-Path : {A : Precategory i₁ i₂} {B : Precategory i₃ i₄} {F G : Functor A B} {α β : NaturalTransformation F G}
                             → pr₁ (naturaltransformation-rec→sig F G α) ≡ pr₁ (naturaltransformation-rec→sig F G β)
                             → α ≡ β
NaturalTransformation-Path {B = B} x =
  equiv-types-eq
    NaturalTransformation-sig-Equiv
    (path-equiv-sigma (x ,
      (implicit-funext (λ a →
        implicit-funext λ b →
        funextD λ f →
          HomSet B _ _ _ _ _ _))))

-- | As natural transformations are a sigma type with fibres props, they form a set.
NaturalTransformation-is-set : {A : Precategory i₁ i₂} {B : Precategory i₃ i₄} {F G : Functor A B}
                               → isSet (NaturalTransformation F G)
NaturalTransformation-is-set {B = B} =
  equiv-with-set
    NaturalTransformation-sig-Equiv
    (prop-fibres-totalspace-set
      (fibs-are-sets-PI-is-set (λ a → HomSet B _ _))
      λ a P Q →
        implicit-funext λ x →
        implicit-funext λ y →
        funextD λ f →
          HomSet B _ _ _ _ _ _)

-- There is an identity natural transformation.
Id-Nat : {A : Precategory i₁ i₂} {B : Precategory i₃ i₄} {F : Functor A B}
         → NaturalTransformation F F
Id-Nat {B = B} {F = F} = record { α-ob = λ x → Id B
                                ; α-nat = λ f → IdR B (F₁ F f) ∘ IdL B (F₁ F f) ^
                                }

_<o>N_ : {A : Precategory i₁ i₂} {B : Precategory i₃ i₄} {F G H : Functor A B}
         (β : NaturalTransformation G H)
         (α : NaturalTransformation F G)
         → NaturalTransformation F H
_<o>N_ {B = B} {F = F} {G = G} {H = H }β α =
  record { α-ob = λ a → α-ob β a o⟨ B ⟩ α-ob α a
         ; α-nat = λ {x} {y} f → Assoc B (F₁ F f) (α-ob α y) (α-ob β y) ^
                                 ∘ precat-whiskerL B (α-nat α f) (α-ob β y)
                                 ∘ Assoc B (α-ob α x) (F₁ G f) (α-ob β y)
                                 ∘ precat-whiskerR B (α-nat β f) (α-ob α x)
                                 ∘ Assoc B (α-ob α x) (α-ob β x) (F₁ H f) ^ }


infixr 9 _<o>N_

α-o-Id : {A : Precategory i₁ i₂} {B : Precategory i₃ i₄} {F G : Functor A B} {α : NaturalTransformation F G}
         → α <o>N Id-Nat ≡ α
α-o-Id {B = B} {α = α}= NaturalTransformation-Path (funextD λ a → IdL B (α-ob α a))

Id-o-α : {A : Precategory i₁ i₂} {B : Precategory i₃ i₄} {F G : Functor A B} {α : NaturalTransformation F G}
         → Id-Nat <o>N α ≡ α
Id-o-α {B = B} {α = α} = NaturalTransformation-Path (funextD λ a → IdR B (α-ob α a))


N-assoc : {A : Precategory i₁ i₂} {B : Precategory i₃ i₄} {F G H K : Functor A B}
          (α : NaturalTransformation F G)
          (β : NaturalTransformation G H)
          (γ : NaturalTransformation H K)
          → γ <o>N β <o>N α ≡ (γ <o>N β) <o>N α
N-assoc {B = B} α β γ =
  NaturalTransformation-Path
    (funextD λ x →
      Assoc B (α-ob α x) (α-ob β x) (α-ob γ x))
