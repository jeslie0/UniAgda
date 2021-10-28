{-# OPTIONS --without-K --no-import-sorts #-}
module Category where

open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Functions
open import UniAgda.Core.Types.Sigma
open import UniAgda.Core.Types.Identity

open import UniAgda.Core.SetsAndLogic.ContrPropSet1Type
open import UniAgda.Core.SetsAndLogic.Props
open import UniAgda.Core.SetsAndLogic.Sets
open import UniAgda.Core.SetsAndLogic.Equivalences

open import UniAgda.Core.Homotopy
open import UniAgda.Core.Equivalences

open import UniAgda.Core.PathSpaces.Sigma
open import UniAgda.Core.PathAlgebra

open import UniAgda.Core.Axioms

private
  variable
    i₁ i₂ i₃ i₄ : Level

-- Precategory definition
record Precategory (i₁ i₂ : Level) : Type (lsuc (i₁ ⊔ i₂)) where
  eta-equality
  field
    Ob : Type i₁
    Hom : (a b : Ob) → Type i₂
    Id : {a : Ob} → (Hom a a)
    Comp : {a b c : Ob} → (Hom b c) → Hom a b → Hom a c

  _<o>_ = Comp

  field
    HomSet : (a b : Ob) → isSet (Hom a b)
    IdL : {a b : Ob} (f : Hom a b) → f <o> Id ≡ f
    IdR : {a b : Ob} (f : Hom a b) → Id <o> f ≡ f
    Assoc : {a b c d : Ob} (f : Hom a b) (g : Hom b c) (h : Hom c d) → h <o> (g <o> f) ≡ (h <o> g) <o> f



open Precategory

-- Syntax
_[_,_] : (C : Precategory i₁ i₂) → (x y : C .Ob) → Type i₂
C [ x , y ] = C .Hom x y

Comp' : (C : Precategory i₁ i₂) {a b c : C .Ob}
        → C [ b , c ]
        → C [ a , b ]
        → C [ a , c ]
Comp' = Comp

infixr 15 Comp'
syntax Comp' C g f = g o⟨ C ⟩ f


-- Isomorphisms
isIso : (C : Precategory i₁ i₂) {a b : C .Ob} (f : C [ a , b ]) → Type i₂
isIso C {a = a} {b = b} f = Σ[ g ∈ C [ b , a ] ] ((f o⟨ C ⟩ g ≡ C .Id) × (g o⟨ C ⟩ f ≡ C .Id))

iso : (C : Precategory i₁ i₂) (a b : C .Ob)
      → Type i₂
iso C a b = Σ[ f ∈ (C [ a , b ]) ] (isIso C f)
syntax iso C a b = a ≅⟨ C ⟩ b

-- "iso" is an equivalence relation.
iso-refl : (C : Precategory i₁ i₂) {a : C .Ob}
           → a ≅⟨ C ⟩ a
iso-refl C {a = a} = Id C , (Id C) , IdR C (Id C) , IdL C (Id C)

iso-sym : (C : Precategory i₁ i₂) {a b : C .Ob}
          → a ≅⟨ C ⟩ b
          → b ≅⟨ C ⟩ a
iso-sym C (f , g , α , β) = (g , f , β , α)

iso-trans : (C : Precategory i₁ i₂) {a b c : C .Ob}
            → a ≅⟨ C ⟩ b
            → b ≅⟨ C ⟩ c
            → a ≅⟨ C ⟩ c
iso-trans C (f , f' , α , α') (g , g' , β , β') =
  g o⟨ C ⟩ f ,
  f' o⟨ C ⟩ g' ,
  Assoc C g' f' (Comp' C g f) ∘
    transport
      (λ z → z o⟨ C ⟩ g' ≡ C .Id) (Assoc C f' f g)
      (transport (λ z → (g o⟨ C ⟩ z) o⟨ C ⟩ g' ≡ C .Id) (α ^)
        (transport (λ z → z o⟨ C ⟩ g' ≡ C .Id) (IdL C g ^) β)) ,
  Assoc C (Comp' C g f) g' f' ^ ∘
    transport (λ z → f' o⟨ C ⟩ z ≡ C .Id) (Assoc C f g g' ^)
      (transport (λ z → f' o⟨ C ⟩ (z o⟨ C ⟩ f) ≡ C .Id) (β' ^)
        (transport (λ z → f' o⟨ C ⟩ z ≡ C .Id) (IdR C f ^) α'))


-- isIso is a proposition, so we have a set of isomorphisms.
isIso-is-prop : (C : Precategory i₁ i₂) {a b : C .Ob}
                (f : C [ a , b ])
                → isProp (isIso C f)
isIso-is-prop C f (g , α , β) (g' , α' , β') =
  path-equiv-sigma (IdR C g ^
                   ∘ transport (λ z → z o⟨ C ⟩ g ≡ g') β'
                     (Assoc C g f g' ^
                     ∘ transport (λ z → g' o⟨ C ⟩ z ≡ g') (α ^)
                       (IdL C g')) ,
    path-equiv-prod (HomSet C _ _ _ _ _ _ ,
      HomSet C _ _ _ _ _ _))

iso-is-set : (C : Precategory i₁ i₂) {a b : C .Ob}
             → isSet (a ≅⟨ C ⟩ b)
iso-is-set C {a} {b} =
  prop-fibres-totalspace-set
    (HomSet C a b)
    λ f → isIso-is-prop C f


-- We can convert a path in a category into an isomorphism
id-to-iso : (C : Precategory i₁ i₂) {a b : C .Ob}
            → (a ≡ b)
            → (a ≅⟨ C ⟩ b)
id-to-iso C refl =
  (Id C) ,
  (Id C) ,
  (IdL C (C .Id)) ,
  (IdR C (C .Id))

-- Whiskering
precat-whiskerL : (C : Precategory i₁ i₂) {x y z : C .Ob} {f g : C [ x , y ]}
                  (p : f ≡ g) (h : C [ y , z ])
                  → h o⟨ C ⟩ f ≡ h o⟨ C ⟩ g
precat-whiskerL C refl h = refl


precat-whiskerR : (C : Precategory i₁ i₂) {x y z : C .Ob} {f g : C [ y , z ]}
                  (p : f ≡ g) (h : C [ x , y ])
                     → f o⟨ C ⟩ h ≡ g o⟨ C ⟩ h
precat-whiskerR C refl h = refl

-- Categories
-- A category is a univalent precategory
isCategory : (C : Precategory i₁ i₂)
             → Type (i₁ ⊔ i₂)
isCategory C =
  (a b : C .Ob) → isEquiv (id-to-iso C {a} {b})

Category : (i j : Level) → Type (lsuc i ⊔ lsuc j)
Category i j = Σ[ C ∈ Precategory i j ] isCategory C

isCategory-is-prop : (C : Precategory i₁ i₂)
                     → isProp (isCategory C)
isCategory-is-prop C =
  prop-fibres-Pi-is-prop
    λ x → prop-fibres-Pi-is-prop
    λ y →  isEquiv-is-prop (id-to-iso C)


iso-to-id : (C : Precategory i₁ i₂) (univ : isCategory C) {a b : C .Ob}
            → (a ≅⟨ C ⟩ b)
            → a ≡ b
iso-to-id C univ {a = a} {b = b} x = pr₁ (univ a b) x

iso-id-equiv : (C : Precategory i₁ i₂) (univ : isCategory C) {a b : C .Ob}
               → (a ≅⟨ C ⟩ b) ≃ (a ≡ b)
iso-id-equiv C univ {a} {b} =
  equiv-adjointify
    (iso-to-id C univ ,
    id-to-iso C ,
    (pr₁ $ pr₂ (univ a b)) ,
    pr₁ (pr₂ (pr₂ (univ a b))))

cat-ob-is1type : (C : Precategory i₁ i₂) (univ : isCategory C)
                 → is1type (C .Ob)
cat-ob-is1type C univ a b =
  equiv-with-set
    (iso-id-equiv C univ)
    (iso-is-set C)


module Precategory-Σ-Equivalence where


-- Equality of categories
-- Two precategories are equal when they agree on Objects, Hom, Ids and Comp.

  Precategory-sig : (i j : Level) → Type (lsuc (i ⊔ j))
  Precategory-sig i j =
    Σ[ ObHomIdComp ∈ (Σ[ Ob ∈ (Type i) ]
                         Σ[ Hom ∈ ((a b : Ob) → Type j) ]
                           Σ[ Id ∈ ({a : Ob} → (Hom a a)) ]
                             ({a b c : Ob} → (Hom b c) → Hom a b → Hom a c)) ]
       Σ[ HomSet ∈ ((a b : pr₁ ObHomIdComp) → isSet ((pr₁ $ pr₂ ObHomIdComp) a b)) ]
         Σ[ l-Id ∈ ({a b : (pr₁ ObHomIdComp)} (f : (pr₁ $ pr₂ ObHomIdComp) a b) → pr₂ (pr₂ (pr₂ ObHomIdComp)) f (pr₁ (pr₂ (pr₂ ObHomIdComp))) ≡ f) ]
           Σ[ r-Id ∈ ({a b : (pr₁ ObHomIdComp)} (f : (pr₁ (pr₂ ObHomIdComp)) a b) → (pr₂ (pr₂ (pr₂ ObHomIdComp))) (pr₁ (pr₂ (pr₂ ObHomIdComp))) f ≡ f) ]
             ({a b c d : (pr₁ ObHomIdComp)} (f : (pr₁ (pr₂ ObHomIdComp)) a b) (g : (pr₁ (pr₂ ObHomIdComp)) b c) (h : (pr₁ (pr₂ ObHomIdComp)) c d) → (pr₂ (pr₂ (pr₂ ObHomIdComp))) h ((pr₂ (pr₂ (pr₂ ObHomIdComp))) g f) ≡ (pr₂ (pr₂ (pr₂ ObHomIdComp))) ((pr₂ (pr₂ (pr₂ ObHomIdComp))) h g) f)

  precategory-rec→sig : Precategory i₁ i₂ → Precategory-sig i₁ i₂
  precategory-rec→sig record { Ob = Ob
                             ; Hom = Hom
                             ; Id = Id
                             ; Comp = Comp
                             ; HomSet = HomSet
                             ; IdL = IdL
                             ; IdR = IdR
                             ; Assoc = Assoc
                             } =
                      (Ob , Hom , Id , Comp) , HomSet , IdL , IdR , Assoc

  precategory-sig→rec : Precategory-sig i₁ i₂ → Precategory i₁ i₂
  precategory-sig→rec ((Ob , Hom , Id , Comp) , HomSet , IdL , IdR , Assoc) = record { Ob = Ob
                                                                                     ; Hom = Hom
                                                                                     ; Id = Id
                                                                                     ; Comp = Comp
                                                                                     ; HomSet = HomSet
                                                                                     ; IdL = IdL
                                                                                     ; IdR = IdR
                                                                                     ; Assoc = Assoc
                                                                                     }

  precategory-sig→rec→sig : (C : Precategory-sig i₁ i₂)
                            → (precategory-rec→sig o precategory-sig→rec) C ≡ C
  precategory-sig→rec→sig ((Ob , Hom , Id , Comp) , HomSet , IdL , IdR , Assoc) =
    path-equiv-sigma ((path-equiv-sigma (refl ,
                     (path-equiv-sigma (refl ,
                       (path-equiv-sigma (refl ,
                         refl)))))) ,
                     (path-equiv-sigma (refl ,
                     (path-equiv-sigma (refl ,
                     (path-equiv-sigma (refl ,
                     refl)))))))

  precategory-rec→sig→rec : (C : Precategory i₁ i₂)
                            → (precategory-sig→rec o precategory-rec→sig) C ≡ C
  precategory-rec→sig→rec C = refl

  Precategory-Σ-Equiv : Precategory-sig i₁ i₂ ≃ Precategory i₁ i₂
  Precategory-Σ-Equiv =
    equiv-adjointify
      ( precategory-sig→rec
      , precategory-rec→sig
      , precategory-rec→sig→rec
      , precategory-sig→rec→sig)

  Precategory-Path : {A B : Precategory i₁ i₂}
                     → pr₁ (precategory-rec→sig A) ≡ pr₁ (precategory-rec→sig B)
                     → A ≡ B
  Precategory-Path {B = B} p =
    equiv-types-eq
      Precategory-Σ-Equiv
      (path-equiv-sigma (p ,
        (path-equiv-sigma (prop-fibres-Pi-is-prop
                          (λ x → prop-fibres-Pi-is-prop λ y → isSet-is-prop _) _ _  ,
                          (path-equiv-sigma (implicit-funext (λ x →
                            implicit-funext λ y →
                              prop-fibres-Pi-is-prop (λ f → HomSet B _ _ _ _) _ _) ,
                          (path-equiv-sigma (implicit-funext (λ x →
                                            implicit-funext λ y →
                                            prop-fibres-Pi-is-prop (λ f → HomSet B _ _ _ _) _ _) ,
                          implicit-funext λ x →
                          implicit-funext λ y →
                          implicit-funext λ z →
                          implicit-funext λ w →
                          prop-fibres-Pi-is-prop
                          (λ f → prop-fibres-Pi-is-prop
                          λ g → prop-fibres-Pi-is-prop
                          λ h → HomSet B _ _ _ _) _ _))))))))

open Precategory-Σ-Equivalence

-- Opposite Precategory

_ᵒᵖ : Precategory i₁ i₂ → Precategory i₁ i₂
Ob (C ᵒᵖ) = C .Ob
Hom (C ᵒᵖ) a b = C [ b , a ]
HomSet (C ᵒᵖ) a b = C .HomSet b a
Id (C ᵒᵖ) = C .Id
Comp (C ᵒᵖ) f g = g o⟨ C ⟩ f
IdL (C ᵒᵖ) = C .IdR
IdR (C ᵒᵖ) = C .IdL
Assoc (C ᵒᵖ) f g h = Assoc C h g f ^

op-involution : (C : Precategory i₁ i₂)
                → (C ᵒᵖ) ᵒᵖ ≡ C
op-involution C =
  Precategory-Path
    (path-equiv-sigma (refl ,
      (path-equiv-sigma (refl ,
        (path-equiv-sigma (refl ,
          refl))))))
