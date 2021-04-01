{-# OPTIONS --without-K --rewriting --no-import-sorts #-}
module UniAgda.experimental.exp6 where

open import UniAgda.Core.Everything
open import UniAgda.Categories.Everything
open import UniAgda.Categories.FunctorCat


open Precategory

F-id-type-is-prop : ∀ {i₁ i₂ i₃ i₄} {A : Precategory i₁ i₂} {B : Precategory i₃ i₄}
                    (F : Functor A B)
                    → isProp ({a : A .ob} → Functor.F₁ F (A .Id) ≡ B .Id)
F-id-type-is-prop {A = A} {B = B} F x y =
  let module A = Precategory A
      module B = Precategory B
      module F = Functor F
  in
  implicit-funext λ a →
    B.hom-set (F.F₀ a) (F.F₀ a) (F.F₁ A.Id) (B .Id) x y

F-comp-type-is-prop : ∀ {i₁ i₂ i₃ i₄} {A : Precategory i₁ i₂} {B : Precategory i₃ i₄}
                      (F : Functor A B)
                      → isProp ({a b c : A .ob} (g : A [ b , c ]) (f : A [ a , b ]) →
      Functor.F₁ F (comp' A g f) ≡
      comp' B (Functor.F₁ F g) (Functor.F₁ F f))
F-comp-type-is-prop {A = A} {B = B} F x y =
  let module A = Precategory A
      module B = Precategory B
      module F = Functor F
  in
  implicit-funext λ a →
  implicit-funext λ b →
  implicit-funext λ c →
  funextD λ f →
  funextD λ g →
    B.hom-set
      (F.F₀ a)
      (F.F₀ c)
      (F.F₁ (comp' A f g))
      (comp' B (F.F₁ f) (F.F₁ g))
      (x f g)
      (y f g)



      -- Σ[ F₀ ∈ ((A.ob) → (B.ob))] (
      --   Σ[ F₁ ∈ ({a b : A.ob} → A.hom a b → B.hom (F₀ a) (F₀ b))] (
      --     Σ[ F-id ∈ ({a : A.ob} → F₁ (A.Id {a}) ≡ (B.Id {F₀ a}))] (
      --       ({a b c : A.ob} (g : A.hom b c) (f : A.hom a b) → F₁ (A.comp g f) ≡ B.comp (F₁ g) (F₁ f)))))


Functor-swapsig : ∀ {i₁ i₂ i₃ i₄} (A : Precategory i₁ i₂) (B : Precategory i₃ i₄)
                  → Type (i₁ ⊔ i₂ ⊔ i₃ ⊔ i₄)
Functor-swapsig A B =
  (Σ[ F₀F₁ ∈ (Σ[ F₀ ∈ (A .ob → B .ob) ] (({a b : A .ob} → A .hom a b → B .hom (F₀ a) (F₀ b)))) ]
    Σ[ F-Id ∈ ( ({a : A .ob} → pr₂ F₀F₁ (A .Id {a}) ≡ (B .Id {pr₁ F₀F₁ a}))) ]
       (({a b c : A .ob} (g : A .hom b c) (f : A .hom a b) → (pr₂ F₀F₁) (A .comp g f) ≡ B .comp ((pr₂ F₀F₁) g) ((pr₂ F₀F₁) f))))




lemma : ∀ {i₁ i₂ i₃ i₄} {A : Precategory i₁ i₂} {B : Precategory i₃ i₄}
         → (Functor-sig A B) ≃ (Functor-swapsig A B)
lemma {i₁} {i₂} {i₃} {i₄} {A} {B} =
  let module A = Precategory A
      module B = Precategory B
  in
  equiv-adjointify
    ((λ { (F₀ , F₁ , F-id , F-comp) → (F₀ , F₁) , (F-id , F-comp)}) ,
    (λ { ((F₀ , F₁) , (F-id , F-comp)) → F₀ , F₁ , F-id , F-comp}) ,
    (λ { ((F₀ , F₁) , (F-id , F-comp)) → path-equiv-sigma (refl , (path-equiv-sigma (refl , refl)))}) ,
    λ { (F₀ , F₁ , F-id , F-comp) → path-equiv-sigma (refl , (path-equiv-sigma (refl , (path-equiv-sigma (refl , refl)))))})
  

lemma2 : ∀ {i₁ i₂ i₃ i₄} {A : Precategory i₁ i₂} {B : Precategory i₃ i₄}
         (F G : Functor-swapsig A B)
         → pr₁ F ≡ pr₁ G → (F ≡ G)
lemma2 {A = A} {B = B} F G p =
  path-equiv-sigma (p ,
    (path-equiv-sigma (implicit-funext (λ x → B .hom-set (pr₁ (pr₁ G) x) (pr₁ (pr₁ G) x) (pr₂ (pr₁ G) (A .Id)) (B .Id) _ (pr₁ (pr₂ G)))  ,
      implicit-funext λ a →
      implicit-funext λ b →
      implicit-funext λ c →
      funextD λ f →
      funextD λ g → B .hom-set (pr₁ (pr₁ G) a) (pr₁ (pr₁ G) c) (pr₂ (pr₁ G) (A .comp f g)) (B .comp (pr₂ (pr₁ G) f) (pr₂ (pr₁ G) g)) _ (pr₂ (pr₂ G) f g))))

lemma3 : ∀ {i₁ i₂ i₃ i₄} {A : Precategory i₁ i₂} {B : Precategory i₃ i₄}
         {F G : Functor A B}
         → pr₁ (lemma {A = A} {B = B}) (functor-rec→sig F) ≡ pr₁ (lemma {A = A} {B = B}) (functor-rec→sig G) → F ≡ G
lemma3 {A = A} {B = B} p =
  equiv-types-eq
    Functor-sig-Equiv
    (equiv-types-eq
      (lemma {A = A} {B = B} ^ᵉ)
      p)


lemma9-1-9-redone : ∀ {i₁ i₂} {A : Precategory i₁ i₂} {a a' b b' : A .ob}
                    (p : a ≡ a') (q : b ≡ b')
                    → transport (A .hom {!!}) {!!} {!!}  ≡ {!!}
lemma9-1-9-redone {A = A} = {!!}


curryD : ∀ {i j} {A : Type i}
         (B : A → A → Type j)
         → A × A → Type j
curryD B (a , b) = B b b


hehe : ∀ {i j k} {X : Type i} {x₁ x₂ : X}
       (A : X → Type j) (B : X → Type k) (p : x₁ ≡ x₂) (f : A x₁ → B x₁)
       → transport (λ x → A x → B x) p f ≡ λ x → transport B p (f (transport A (p ^) x))
hehe A B refl f = refl

haha : ∀ {i j k} {X : Type i} {x₁ x₂ : X}
       (A : X → Type j) (B : (x : X) → A x → Type k) (p : x₁ ≡ x₂) (f : (a : A x₁) → B x₁ a)
       → (a : A x₂) → transport (λ x → (a : A x) → B x a) p f a ≡ transport (λ (w : Σ[ x ∈ X ] A x) → B (pr₁ w) (pr₂ w)) (path-equiv-sigma ((p ^) , refl) ^) (f (transport A (p ^) a))
haha A B refl f a = refl

open NaturalTransformation
open Functor

help : ∀ {i₁ i₂ i₃ i₄} {A : Precategory i₁ i₂} {B : Precategory i₃ i₄}
       (univB : isCategory B) (F G : (B ^ A) .ob)
       → iso (B ^ A) F G → F .F₀ ≡ G .F₀
help univB F G γ = funextD λ x → pr₁ (univB (F .F₀ x) (G .F₀ x)) (pr₁ γ .α-ob x , pr₁ (nat-trans-iso-components (pr₁ γ)) (pr₂ γ) x) 


help1 : ∀ {i₁ i₂ i₃ i₄} {A : Precategory i₁ i₂} {B : Precategory i₃ i₄}
       (univB : isCategory B) (F G : (B ^ A) .ob) (γ : iso (B ^ A) F G) (a : A .ob)
       → happlyD (help univB F G γ) a ≡ pr₁ (univB (F .F₀ a) (G .F₀ a)) ((pr₁ γ .α-ob a) ,  pr₁ (nat-trans-iso-components (pr₁ γ)) (pr₂ γ) a)
help1 univB F G γ a = {!!}


functor-cat-γ' : ∀ {i₁ i₂ i₃ i₄} {A : Precategory i₁ i₂} {B : Precategory i₃ i₄}
                 (univB : isCategory B) (F G : (B ^ A) .ob)
                 → iso (B ^ A) F G → F ≡ G
functor-cat-γ' {A = A} {B = B} univB F G γ =
  let module A = Precategory A
      module B = Precategory B
      module F = Functor F
      module G = Functor G
      γ' = help univB F G γ
  in
  lemma3
    (path-equiv-sigma (
      path-equiv-sigma (γ' ,
        implicit-funext λ a →
        implicit-funext λ b →
          {!haha !}) ,
      path-equiv-sigma ((F-id-type-is-prop G _ G.F-id) ,
        F-comp-type-is-prop G _ G.F-comp)))
