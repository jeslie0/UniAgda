{-# OPTIONS --without-K --rewriting --no-import-sorts #-}
module UniAgda.experimental.exp6 where

open import UniAgda.Core.Everything
open import UniAgda.Categories.Category
open import UniAgda.Categories.Functor
-- open import UniAgda.Categories.FunctorCat


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

uncurry : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
         (f : A → B → C)
         → A × B → C
uncurry f (a , b) = f a b
uncurryD : ∀ {i j} {A : Type i}
         (B : A → A → Type j)
         → A × A → Type j
uncurryD B (a , b) = B b b





implicit-explicit-families : ∀ {i j} {A : Type i}
                             (B : {a : A} → Type j)
                             → (a : A) → Type j
implicit-explicit-families B a = B {a}

explicit→implicit-families : ∀ {i j} {A : Type i}
                             (B : (a : A) → Type j)
                             → {a : A} → Type j
explicit→implicit-families B {a} = B a


-- open NaturalTransformation
-- open Functor

-- help : ∀ {i₁ i₂ i₃ i₄} {A : Precategory i₁ i₂} {B : Precategory i₃ i₄}
--        (univB : isCategory B) (F G : (B ^ A) .ob)
--        → iso (B ^ A) F G → F .F₀ ≡ G .F₀
-- help univB F G γ = funextD λ x → pr₁ (univB (F .F₀ x) (G .F₀ x)) (pr₁ γ .α-ob x , pr₁ (nat-trans-iso-components (pr₁ γ)) (pr₂ γ) x)


-- help1 : ∀ {i₁ i₂ i₃ i₄} {A : Precategory i₁ i₂} {B : Precategory i₃ i₄}
--        (univB : isCategory B) (F G : (B ^ A) .ob) (γ : iso (B ^ A) F G) (a : A .ob)
--        → happlyD (help univB F G γ) a ≡ pr₁ (univB (F .F₀ a) (G .F₀ a)) ((pr₁ γ .α-ob a) ,  pr₁ (nat-trans-iso-components (pr₁ γ)) (pr₂ γ) a)
-- help1 univB F G γ a = {!!}


-- test : ∀ {i₁ i₂ i₃ i₄} {A : Precategory i₁ i₂} {B : Precategory i₃ i₄}
--        → (λ F₂ → {a b : A .ob} → A .hom a b → B .hom (F₂ a) (F₂ b))
--          ≡ (λ F₂ → (a b : A .ob) → A .hom a b → B .hom (F₂ a) (F₂ b))
-- test {i₁} {i₂} {i₃} {i₄} {A} {B} = {!!}


-- lemma2-3-11 : ∀ {i j k} {A : Type i} {x y : A} {P : A → Type j} {Q : A → Type k}
--               (f : (x : A) → P x → Q x) (p : x ≡ y) (u : P x)
--               → transport Q p (f x u) ≡ f y (transport P p u)
-- lemma2-3-11 f refl u = refl





-- functor-cat-γ' : ∀ {i₁ i₂ i₃ i₄} {A : Precategory i₁ i₂} {B : Precategory i₃ i₄}
--                  (univB : isCategory B) (F G : (B ^ A) .ob)
--                  → iso (B ^ A) F G → F ≡ G
-- functor-cat-γ' {A = A} {B = B} univB F G γ =
--   let module A = Precategory A
--       module B = Precategory B
--       module F = Functor F
--       module G = Functor G
--       γ' = help univB F G γ
--   in
--   lemma3
--     (path-equiv-sigma (
--       path-equiv-sigma (γ' ,
--             implicit-funext λ a →
--             implicit-funext λ b →
--                {!!}) ,
--       path-equiv-sigma ((F-id-type-is-prop G _ G.F-id) ,
--         F-comp-type-is-prop G _ G.F-comp)))


-- foo : ∀ {i j} {A : Type i} {C : A → A → Type j} {a a' b b' : A}
--       (p : a ≡ a') (q : b ≡ b') (f : C a b)
--       → transport (uncurry C) (path-equiv-prod (p , q)) f ≡ transport (λ x → transport (λ y → {!C x y!}) {!!} {!!}) p {!!}
-- foo p q f = {!!}



-- Functor-sig-exp : ∀ {i j k l}
--           (A : Precategory i j) (B : Precategory k l)
--           → Type (i ⊔ j ⊔ k ⊔ l)
-- Functor-sig-exp {i} {j} {k} {l} A B =
--   let module A = Precategory A in
--     let module B = Precategory B in
--       Σ[ F₀ ∈ ((A.ob) → (B.ob))] (
--         Σ[ F₁ ∈ ((a b : A.ob) → A.hom a b → B.hom (F₀ a) (F₀ b))] (
--           Σ[ F-id ∈ ((a : A.ob) → F₁ a a A.Id ≡ (B.Id {F₀ a}))] (
--             ((a b c : A.ob) (g : A.hom b c) (f : A.hom a b) → F₁ a c (A.comp g f) ≡ B.comp (F₁ b c g) (F₁ a b f)))))


-- Functor-sig-exp→rec : ∀ {i j k l}
--                     {A : Precategory i j} {B : Precategory k l}
--                     → Functor-sig-exp A B → Functor A B
-- Functor.F₀ (Functor-sig-exp→rec (F₀ , F₁ , F-id , F-comp)) = F₀
-- Functor.F₁ (Functor-sig-exp→rec (F₀ , F₁ , F-id , F-comp)) {a} {b} x = F₁ a b x
-- Functor.F-id (Functor-sig-exp→rec (F₀ , F₁ , F-id , F-comp)) {a} = F-id a
-- Functor.F-comp (Functor-sig-exp→rec (F₀ , F₁ , F-id , F-comp)) {a} {b} {c} g f = F-comp a b c g f

-- Functor-rec→sig-exp : ∀ {i j k l}
--                       {A : Precategory i j} {B : Precategory k l}
--                       → Functor A B → Functor-sig-exp A B
-- Functor-rec→sig-exp record { F₀ = F₀ ; F₁ = F₁ ; F-id = F-id ; F-comp = F-comp } =
--   F₀ ,
--   ((λ a b → F₁) ,
--   ((λ a → F-id) ,
--   (λ a b c → F-comp)))

-- lol : ∀ {i j k l}
--       {A : Precategory i j} {B : Precategory k l}
--       → Functor-sig-exp→rec o Functor-rec→sig-exp ~ id
-- lol record { F₀ = F₀ ; F₁ = F₁ ; F-id = F-id ; F-comp = F-comp } =
--   refl

-- lol' : ∀ {i j k l}
--      {A : Precategory i j} {B : Precategory k l}
--      → Functor-rec→sig-exp o Functor-sig-exp→rec ~ id
-- lol' x =
--   path-equiv-sigma (refl ,
--     (path-equiv-sigma (refl ,
--       (path-equiv-sigma (refl ,
--         refl)))))


-- func-equiv : ∀ {i j k l}
--              {A : Precategory i j} {B : Precategory k l}
--              → Functor-sig-exp A B ≃ Functor A B
-- func-equiv = equiv-adjointify
--   (Functor-sig-exp→rec , (Functor-rec→sig-exp , (lol , lol')))

-- -- isTypeOf : ∀ {i} {A : Type i}
-- --            (a : A)
-- --            → Type i
-- -- isTypeOf {A = A} a = A

-- -- Func3-is-prop : ∀ {i j k l}
-- --               {A : Precategory i j} {B : Precategory k l}
-- --               → F : Fu
-- --               → isProp ( ((a : A .ob) → F₁ a a A .Id ≡ (B .Id {F₀ a})))
-- -- Func3-is-prop = ?
