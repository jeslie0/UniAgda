{-# OPTIONS --without-K --no-import-sorts #-}
module Functor where

open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Functions
open import UniAgda.Core.Types.Identity
open import UniAgda.Core.Types.Sigma

open import UniAgda.Core.Equivalences
open import UniAgda.Core.Homotopy

open import UniAgda.Core.PathAlgebra

open import UniAgda.Core.SetsAndLogic.ContrPropSet1Type
open import UniAgda.Core.SetsAndLogic.Sets
open import UniAgda.Core.SetsAndLogic.Props

open import UniAgda.Core.PathSpaces.Sigma
open import UniAgda.Core.PathSpaces.Identity

open import UniAgda.Core.Axioms

open import Category
open Precategory

private
  variable
    i₁ i₂ i₃ i₄ : Level


record Functor (A : Precategory i₁ i₂) (B : Precategory i₃ i₄) : Type (i₁ ⊔ i₂ ⊔ i₃ ⊔ i₄) where
  eta-equality
  field
    F₀ : A .Ob → B .Ob
    F₁ : {a b : A .Ob} → A [ a , b ] →  B [ (F₀ a) , (F₀ b) ]
    F-id : {a : A .Ob} → F₁ (A .Id {a}) ≡ (B .Id {F₀ a})
    F-comp : {a b c : A .Ob} (g : A [ b , c ]) (f : A [ a , b ]) → F₁ (g o⟨ A ⟩ f) ≡ (F₁ g) o⟨ B ⟩ (F₁ f)

  ₀ = F₀
  ₁ = F₁

open Functor

-- Sigma definition
module Functor-Σ-Equivalence where
  Functor-sig : (A : Precategory i₁ i₂) (B : Precategory i₃ i₄)
                → Type (i₁ ⊔ i₂ ⊔ i₃ ⊔ i₄)
  Functor-sig A B = Σ[ F₀F₁ ∈ (Σ[ F₀ ∈ (A .Ob → B .Ob) ]
                                  ({a b : A .Ob} → A [ a , b ] → B [ F₀ a , F₀ b ])) ]
                                  Σ[ F-Id ∈ ({a : A .Ob} → (pr₂ F₀F₁) (A .Id {a}) ≡ (B .Id {(pr₁ F₀F₁) a})) ]
                                    ( {a b c : A .Ob} (g : A [ b , c ]) (f : A [ a , b ]) → (pr₂ F₀F₁) (g o⟨ A ⟩ f) ≡ ((pr₂ F₀F₁) g) o⟨ B ⟩ ((pr₂ F₀F₁) f))

  functor-sig→rec : {A : Precategory i₁ i₂} {B : Precategory i₃ i₄}
                    → Functor-sig A B → Functor A B
  functor-sig→rec ((f₀ , f₁) , f-id , f-comp) = record { F₀ = f₀
                                                       ; F₁ = f₁
                                                       ; F-id = f-id
                                                       ; F-comp = f-comp }

  functor-rec→sig : {A : Precategory i₁ i₂} {B : Precategory i₃ i₄}
                    → Functor A B → Functor-sig A B
  functor-rec→sig record { F₀ = F₀
                         ; F₁ = F₁
                         ; F-id = F-id
                         ; F-comp = F-comp
                         } = (F₀ , F₁) , (F-id , F-comp)

  functor-rec→sig→rec : {A : Precategory i₁ i₂} {B : Precategory i₃ i₄}
                        (F : Functor A B)
                        → (functor-sig→rec o functor-rec→sig) F ≡ F
  functor-rec→sig→rec F = refl

  functor-sig→rec→sig : {A : Precategory i₁ i₂} {B : Precategory i₃ i₄}
                        (F : Functor-sig A B)
                        → (functor-rec→sig o functor-sig→rec {A = A} {B = B}) F ≡ F
  functor-sig→rec→sig ((F₀ , F₁) , F-id , F-comp) =
    path-equiv-sigma ((path-equiv-sigma (refl , refl)) ,
      (path-equiv-sigma (refl , refl)))

  Functor-sig-Equiv : {A : Precategory i₁ i₂} {B : Precategory i₃ i₄}
                      → Functor-sig A B ≃ Functor A B
  Functor-sig-Equiv = equiv-adjointify
    (functor-sig→rec ,
    functor-rec→sig ,
    functor-rec→sig→rec ,
    functor-sig→rec→sig)






open Functor-Σ-Equivalence

Functor-Path : {A : Precategory i₁ i₂} {B : Precategory i₃ i₄} {F G : Functor A B}
               (p : Functor.F₀ F ≡ Functor.F₀ G)
               (q : (a b : A .Ob) (f : A [ a , b ]) →
                  transport (λ f₀ → B [ (f₀ a) , (f₀ b) ])
                            p
                            (Functor.F₁ F f)
                  ≡ Functor.F₁ G f)
               → F ≡ G
Functor-Path {A = A} {B = B} {F = record { F₀ = .(Functor.F₀ G)
                                         ; F₁ = F₁
                                         ; F-id = F-id
                                         ; F-comp = F-comp }
                                         } {G = G} refl Q =
             equiv-types-eq
               Functor-sig-Equiv
               (path-equiv-sigma ((path-equiv-sigma (refl ,
                 (implicit-funext (λ a →
                 implicit-funext λ b →
                 funext λ f → Q a b f)))) ,
                 (path-equiv-sigma (implicit-funext (λ a → HomSet B _ _ _ _ _ _) ,
                   implicit-funext λ x →
                   implicit-funext λ y →
                   implicit-funext λ z →
                   funextD λ f →
                   funextD λ g →
                     HomSet B _ _ _ _ _ _) )))

Functor-Path-Hom : {A : Precategory i₁ i₂} {B : Precategory i₃ i₄} {F G : Functor A B}
                   (p : Functor.F₀ F ≡ Functor.F₀ G)
                   → ((a b : Ob A) (f : A [ a , b ])
                   → transport {_} {_} {(B .Ob) × (B .Ob)} {F₀ F a , F₀ F b} {F₀ G a , F₀ G b} (λ X → B [ pr₁ X , pr₂ X ]) (path-equiv-prod ((happly p a) , (happly p b))) (F₁ F f) ≡ F₁ G f)
                → F ≡ G
Functor-Path-Hom {A = A} {B = B} {F = record { F₀ = .(F₀ G)
                                          ; F₁ = F₂
                                          ; F-id = F-id₁
                                          ; F-comp = F-comp₁ }
                                          } {G = G} refl X =
              Functor-Path
                refl
                λ a b f → X a b f


Functor-Paths-sig-Equiv : {A : Precategory i₁ i₂} {B : Precategory i₃ i₄} {F G : Functor A B}
                    → (functor-rec→sig F ≡ functor-rec→sig G) ≃ (F ≡ G)
Functor-Paths-sig-Equiv =
  equiv-adjointify
    ((λ { refl → refl}) ,
    (λ { refl → refl}) ,
    (λ { refl → refl}) ,
    λ { refl → refl})


                -- → (p ≡ q) ≃ (happlyD p ≡ happlyD q)
-- Pi-path-paths = (ap happlyD) , thm2-11-1 (pr₂ (funextD-equiv))






Functor-Path-Paths-sig : {A : Precategory i₁ i₂} {B : Precategory i₃ i₄}
                         (F G : Functor-sig A B)
                         (p q : F ≡ G)
                         → pr₁ (path-sigma (pr₁ (path-sigma p))) ≡ pr₁ (path-sigma (pr₁ (path-sigma q)))
                         → p ≡ q
Functor-Path-Paths-sig {A = A} {B = B} F G p q x =
    pr₁ (Sigma-path-paths ^ᵉ)
      ((pr₁ (Sigma-path-paths ^ᵉ) (x ,
        pr₁ (Pi-path-paths-implicit ^ᵉ) λ a →
        pr₁ (Pi-path-paths-implicit ^ᵉ) λ b →
        pr₁ (Pi-path-paths ^ᵉ) λ f →
          sets-have-prop-ids  _ (HomSet B _ _) _ (pr₂ (pr₁ G) f) _ _)) ,
      pr₁ (Sigma-path-paths ^ᵉ) (props-are-sets
          (prop-fibres-Pi-is-prop-implicit (λ a s t →
            sets-have-prop-ids
              (B .Hom (pr₁ (pr₁ G) a) (pr₁ (pr₁ G) a))
              (HomSet B _ _)
              (pr₂ (pr₁ G) (A .Id))
              (B .Id) _ _) )
            _ _ _ _ ,
        props-are-sets
          (prop-fibres-Pi-is-prop-implicit (λ a →
          prop-fibres-Pi-is-prop-implicit λ b →
          prop-fibres-Pi-is-prop-implicit λ c →
          prop-fibres-Pi-is-prop λ f →
          prop-fibres-Pi-is-prop λ g →
          sets-have-prop-ids (B .Hom (pr₁ (pr₁ G) a) (pr₁ (pr₁ G) c)) (HomSet B _ _) (pr₂ (pr₁ G) (Comp' A f g)) (Comp' B (pr₂ (pr₁ G) f) (pr₂ (pr₁ G) g)))) _ _ _ _))


Functor-Path-Paths : {A : Precategory i₁ i₂} {B : Precategory i₃ i₄}
                     (F G : Functor A B)
                     (p q : F ≡ G)
                     → pr₁ (path-sigma (pr₁ (path-sigma (ap functor-rec→sig p)))) ≡ pr₁ (path-sigma (pr₁ (path-sigma (ap functor-rec→sig q))))
                     → p ≡ q
Functor-Path-Paths {A = A} {B = B} F G p q x =
  let apfp=apfq = Functor-Path-Paths-sig {_} {_} {_} {_} {A} {B}
                  (functor-rec→sig F)
                  (functor-rec→sig G)
                  (ap functor-rec→sig p)
                  (ap functor-rec→sig q) x
  in ap-of-equiv p q functor-rec→sig (pr₂ (Functor-sig-Equiv ^ᵉ)) apfp=apfq


-- Functor composition
private
  variable
    i₅ i₆ i₇ i₈ : Level
    A : Precategory i₁ i₂
    B : Precategory i₃ i₄
    C : Precategory i₅ i₆
    D : Precategory i₇ i₈

-- | Functors can be composed.
_<o>F_ : (G : Functor B C) (F : Functor A B)
         → Functor A C
Functor.F₀ (G <o>F F) = F₀ G o F₀ F
Functor.F₁ (G <o>F F) = F₁ G o F₁ F
Functor.F-id (G <o>F F) = ap (F₁ G) (F-id F)
                          ∘ F-id G
F-comp (G <o>F F) g f = ap (F₁ G) (F-comp F g f)
                        ∘ F-comp G (F₁ F g) (F₁ F f)

infixr 9 _<o>F_

-- | Composition is associative.
F-assoc : (F : Functor A B) (G : Functor B C) (H : Functor C D)
          → H <o>F G <o>F F ≡ (H <o>F G) <o>F F
F-assoc F G H = Functor-Path refl λ a b f → refl

-- | There is an identity functor
Id-Func : Functor A A
F₀ Id-Func = id
F₁ Id-Func = id
F-id Id-Func = refl
F-comp Id-Func g f = refl

F-o-Id : {F : Functor A B}
         → F <o>F Id-Func ≡ F
F-o-Id = Functor-Path refl λ a b f → refl

Id-o-F : {F : Functor A B}
       → Id-Func <o>F F ≡ F
Id-o-F = Functor-Path refl λ a b f → refl
