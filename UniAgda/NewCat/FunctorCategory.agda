{-# OPTIONS --without-K  --no-import-sorts #-}
module FunctorCategory where

open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Functions
open import UniAgda.Core.Types.Identity
open import UniAgda.Core.Types.Sigma
open import UniAgda.Core.Equivalences
open import UniAgda.Core.SetsAndLogic.Props

open import Category
open import Functor
open import Natural-Transformation

open import UniAgda.Core.PathSpaces.Sigma
open import UniAgda.Core.PathSpaces.Identity
open import UniAgda.Core.Homotopy

open import UniAgda.Core.Axioms

open Precategory
open Category
open Functor.Functor
open NaturalTransformation

private
  variable
    i₁ i₂ i₃ i₄ : Level

-- | Given two precategories, we can form the category of functors between them.
_^_ : (B : Precategory i₃ i₄) (A : Precategory i₁ i₂)
      → Precategory (i₃ ⊔ i₄ ⊔ i₁ ⊔ i₂) (i₄ ⊔ i₁ ⊔ i₂)
Ob (B ^ A) = Functor A B
Hom (B ^ A) F G = NaturalTransformation F G
Id (B ^ A) = Id-Nat
Comp (B ^ A)  = _<o>N_
HomSet (B ^ A) F G = NaturalTransformation-is-set
IdL (B ^ A) α = α-o-Id
IdR (B ^ A) α = Id-o-α
Assoc (B ^ A) = N-assoc

-- Isomorphisms in a functor category

-- | Natural isomorphisms are the natural transformations with all components being isomorphisms.
natural-iso-components : {B : Precategory i₃ i₄} {A : Precategory i₁ i₂} {F G : Ob (B ^ A)}
                         (γ : (B ^ A) [ F , G ])
                         → isIso (B ^ A) γ
                         → (a : Ob A) → isIso B (α-ob γ a)
natural-iso-components γ (γ' , η , ϵ) a =
  α-ob γ' a ,
  happlyD (ap (α-ob) η) a ,
  happlyD (ap (α-ob) ϵ) a

naturaltrans-components-iso→natiso : {B : Precategory i₃ i₄} {A : Precategory i₁ i₂} {F G : Ob (B ^ A)}
                                     (γ : (B ^ A) [ F , G ])
                                     → ((a : Ob A) → isIso B (α-ob γ a))
                                     → isIso (B ^ A) γ
naturaltrans-components-iso→natiso {B = B} {F = F} {G = G} record { α-ob = γ₁ ; α-nat = γ₂ } δ =
  record { α-ob = λ a → pr₁ (δ a)
         ; α-nat = λ {a} {b} f →
               (((((((IdL B (pr₁ (δ b) o⟨ B ⟩ G .F₁ f) ^
                 ∘ precat-whiskerL B (pr₁ (pr₂ (δ a)) ^) (pr₁ (δ b) o⟨ B ⟩ G .F₁ f))
                 ∘ Assoc B (pr₁ (δ a)) (γ₁ a) (pr₁ (δ b) o⟨ B ⟩ G .F₁ f))
                 ∘ precat-whiskerR B (Assoc B (γ₁ a) (G .F₁ f) (pr₁ (δ b)) ^) (pr₁ (δ a)))
                 ∘ precat-whiskerR B (precat-whiskerL B (γ₂ f ^) (pr₁ (δ b))) (pr₁ (δ a)))
                 ∘ precat-whiskerR B (Assoc B (F .F₁ f) (γ₁ b) (pr₁ (δ b)) ) (pr₁ (δ a)))
                 ∘ (Assoc B (pr₁ (δ a)) (F .F₁ f) ((pr₁ (δ b)) o⟨ B ⟩ (γ₁ b)) ^))
               ∘ ap (λ v → Comp B v (Comp B (F₁ F f) (pr₁ (δ a)))) (pr₂ (pr₂ (δ b))))
               ∘ IdR B (F .F₁ f o⟨ B ⟩ pr₁ (δ a))},
  NaturalTransformation-Path (funextD (λ a → pr₁ (pr₂ (δ a)))) ,
  NaturalTransformation-Path (funextD λ a → pr₂ (pr₂ (δ a)))


-- Isomorphisms in functor categories allow us to write F(f) as a conjugate.

iso-conjugate-dom : {A : Precategory i₁ i₂} {B : Precategory i₃ i₄} {F G : (B ^ A) .Ob} {x y : A .Ob}
                    (α : iso (B ^ A) F G)
                    (f : A [ x , y ])
                    → F₁ F f ≡ α-ob (pr₁ $ pr₂ α) y o⟨ B ⟩ F₁ G f o⟨ B ⟩ α-ob (pr₁ α) x
iso-conjugate-dom {B = B} {F = F} {y = y} (α , α^ , η , ϵ) f =
  ((IdR B (F₁ F f) ^ ∘ ap (λ Z → Z o⟨ B ⟩ (F₁ F f)) (happlyD (ap (α-ob) ϵ) y ^))
    ∘ Assoc B (F₁ F f) (α-ob α y) (α-ob α^ y) ^) ∘
  precat-whiskerL B (α-nat α f) (α-ob α^ y)

iso-conjugate-cod : {A : Precategory i₁ i₂} {B : Precategory i₃ i₄} {F G : (B ^ A) .Ob} {x y : A .Ob}
                    (α : iso (B ^ A) F G)
                    (f : A [ x , y ])
                    → F₁ G f ≡ α-ob (pr₁ α) y o⟨ B ⟩ F₁ F f o⟨ B ⟩ α-ob (pr₁ (pr₂ α)) x
iso-conjugate-cod {B = B} {F = F} {y = y} (α , α^ , η , ϵ) f =
  iso-conjugate-dom (α^ , α , ϵ , η) f



-- Univalence
-- A big result for functor precategories is that if B is a category, then (B ^ A) is too. We prove this in several steps.




lemma9-1-9 : (A : Precategory i₁ i₂) {a a' b b' : Ob A}
             (p : a ≡ a')
             (q : b ≡ b')
             (f : A [ a , b ])
             → transport {_} {_} {(A .Ob) × (A .Ob)} {(a , b)} {(a' , b')} (λ X → A [ pr₁ X , pr₂ X ]) (path-equiv-prod (p , q)) f ≡ (pr₁ (id-to-iso A q)) o⟨ A ⟩  f o⟨ A ⟩ pr₁ (pr₂ (id-to-iso A p))
lemma9-1-9 A refl refl f =
  IdL A f ^
  ∘ IdR A _ ^



private
  functor-cat-object-func : {A : Precategory i₁ i₂} {B : Precategory i₃ i₄}
                            (univB : isCategory B) (F G : (B ^ A) .Ob)
                            → iso (B ^ A) F G
                            → Functor.F₀ F ≡ Functor.F₀ G
  functor-cat-object-func {A = A} {B = B} univB F G (α , αIsIso) =
    let αIsoComponents = natural-iso-components α αIsIso
    in funext λ a → pr₁ (univB (F₀ F a) (F₀ G a)) (((α-ob α a) , (αIsoComponents a)))

  helper : {A : Precategory i₁ i₂} {B : Precategory i₃ i₄}
           (univB : isCategory B)
           (F G : (B ^ A) .Ob)
           (X : iso (B ^ A) F G)
           → happly (functor-cat-object-func univB F G X) ~ λ a → pr₁ (univB (F₀ F a) (F₀ G a)) (((α-ob (pr₁ X) a) , ( natural-iso-components (pr₁ X) (pr₂ X) a)))
  helper univB F G X@(α , αIsIso) a = happlyD (happly-funext-to-id λ x → pr₁ (univB (F₀ F x) (F₀ G x))
                                                                             (α-ob α x , natural-iso-components α αIsIso x)) a

  helper2 : {A : Precategory i₁ i₂} {B : Precategory i₃ i₄}
            (univB : isCategory B)
            (F G : (B ^ A) .Ob)
            (X : iso (B ^ A) F G)
            (b : Ob A)
            → (pr₁ (id-to-iso B (pr₁ (univB (F₀ F b) (F₀ G b)) (α-ob (pr₁ X) b , natural-iso-components (pr₁ X) (pr₂ X) b)))) ≡  (α-ob (pr₁ X) b)
  helper2 univB F G X b =
    ap pr₁
      (pr₁ (pr₂ (pr₂ (univB (F₀ F b) (F₀ G b)))) (α-ob (pr₁ X) b , natural-iso-components (pr₁ X) (pr₂ X) b))

  helper3 : {A : Precategory i₁ i₂} {B : Precategory i₃ i₄}
            (univB : isCategory B)
            (F G : (B ^ A) .Ob)
            (X : iso (B ^ A) F G)
            (a : Ob A)
            → (pr₁ (pr₂ (id-to-iso B (pr₁ (univB (F₀ F a) (F₀ G a)) (α-ob (pr₁ X) a , natural-iso-components (pr₁ X) (pr₂ X) a))))) ≡ α-ob (pr₁ (pr₂ X)) a
  helper3 univB F G (X@(α , α^ , η , ϵ)) a = transport (λ Z → pr₁ (pr₂ Z) ≡ α-ob α^ a) (pr₁ (pr₂ (pr₂ (univB (F₀ F a) (F₀ G a)))) (α-ob α a ,
                α-ob α^ a , happlyD (ap α-ob η) a , happlyD (ap α-ob ϵ) a) ^) refl

  functor-cat-map-func : {A : Precategory i₁ i₂} {B : Precategory i₃ i₄}
                         (univB : isCategory B)
                         (F G : (B ^ A) .Ob)
                         → iso (B ^ A) F G
                         → F ≡ G
  functor-cat-map-func {A = A} {B = B} univB F G X =
    Functor-Path-Hom
      (functor-cat-object-func univB F G X)
      λ a b f →
        transport (λ Z → transport {_} {_} {(B .Ob) × (B .Ob)} {(F₀ F a) , (F₀ F b)} {(F₀ G a) , (F₀ G b)} (λ X₁ → B [ pr₁ X₁ , pr₂ X₁ ])
      (path-equiv-prod
       (Z ,
        happly (functor-cat-object-func univB F G X) b))
      (F₁ F f)
      ≡
      F₁ G f) (helper univB F G X a ^)
        (transport (λ Z → transport {_} {_} {(B .Ob) × (B .Ob)} {(F₀ F a) , (F₀ F b)} {(F₀ G a) , (F₀ G b)} (λ X₁ → B [ pr₁ X₁ , pr₂ X₁ ])
      (path-equiv-prod
       (pr₁ (univB (F₀ F a) (F₀ G a))
        (α-ob (pr₁ X) a , natural-iso-components (pr₁ X) (pr₂ X) a)
        , Z))
      (F₁ F f)
      ≡ F₁ G f) (helper univB F G X b ^)
        (lemma9-1-9 B (pr₁ (univB (F₀ F a) (F₀ G a))
                        (α-ob (pr₁ X) a , natural-iso-components (pr₁ X) (pr₂ X) a)) (pr₁ (univB (F₀ F b) (F₀ G b))
                                                                                       (α-ob (pr₁ X) b , natural-iso-components (pr₁ X) (pr₂ X) b)) (F₁ F f)
        ∘ transport (λ Z → Comp' B
     Z (Comp' B (F₁ F f)
       (pr₁
        (pr₂
         (id-to-iso B
          (pr₁ (univB (F₀ F a) (F₀ G a))
           (α-ob (pr₁ X) a , natural-iso-components (pr₁ X) (pr₂ X) a))))))
      ≡ F₁ G f) (helper2 univB F G X b ^)
        (transport (λ Z → Comp' B (α-ob (pr₁ X) b)
      (Comp' B (F₁ F f)
       (pr₁
        (pr₂
         (id-to-iso B
          (pr₁ (univB (F₀ F a) (F₀ G a))
           (α-ob (pr₁ X) a , natural-iso-components (pr₁ X) (pr₂ X) a))))))
      ≡ F₁ G f) (helper2 univB F G X a ^) (transport (λ Z → Comp' B (α-ob (pr₁ X) b)
      (Comp' B (F₁ F f) Z) ≡ F₁ G f) (helper3 univB F G X a ^) (iso-conjugate-cod X f ^) ))
        ))

  id-to-iso→iso-to-id→id-to-iso : {A : Precategory i₁ i₂} {B : Precategory i₃ i₄}
                                  (univB : isCategory B)
                                  (F G : (B ^ A) .Ob)
                                  → (functor-cat-map-func univB F G) o id-to-iso (B ^ A) ~ id
  id-to-iso→iso-to-id→id-to-iso {A = A} {B = B} univB F G p =
    Functor-Path-Paths
      F
      G
      ((functor-cat-map-func univB F G o id-to-iso (B ^ A)) p)
      (id p)
      (pr₁ (Pi-path-paths ^ᵉ) λ x →
        {!!})

  iso-to-id→id-to-iso→iso-to-id : {A : Precategory i₁ i₂} {B : Precategory i₃ i₄}
                                  (univB : isCategory B)
                                  (F G : (B ^ A) .Ob)
                                  → id-to-iso (B ^ A) o (functor-cat-map-func univB F G) ~ id
  iso-to-id→id-to-iso→iso-to-id {A = A} {B = B} univB F G (α , αIsIso) =
    fibres-props-eq
      (λ x → isIso-is-prop (B ^ A) x)
      _
      _
      (NaturalTransformation-Path (funextD λ x → {!!}))
