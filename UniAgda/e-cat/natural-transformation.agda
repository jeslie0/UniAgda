{-# OPTIONS --without-K #-}
module UniAgda.e-cat.natural-transformation where

open import UniAgda.e-cat.functors public

record Nat-trans {i j k l : Level} {A : Precategory i j} {B : Precategory k l} (F G : Functor A B) : Type (i ⊔ j ⊔ l) where
  eta-equality
  field
    α-ob : (x : Precategory.ob A) → Precategory.hom B (Functor.F-ob F x) (Functor.F-ob G x)
    α-hom : {x y : Precategory.ob A} (f : Precategory.hom A x y) → Precategory.comp B (α-ob y) (Functor.F-hom F f) ≡ Precategory.comp B (Functor.F-hom G f) (α-ob x)

  α-hom-is-prop : isProp ((x y : Precategory.ob A) (f : Precategory.hom A x y) → Precategory.comp B (α-ob y) (Functor.F-hom F f) ≡ Precategory.comp B (Functor.F-hom G f) (α-ob x))
  α-hom-is-prop f g =
    funextD λ a → funextD λ b → funextD λ x → Precategory.hom-set B _ _ _ _ _ _


Nat-trans-Sig : {i j k l : Level} {A : Precategory i j} {B : Precategory k l}
            (F G : Functor A B)
            → Type (i ⊔ j ⊔ l)
Nat-trans-Sig {i} {j} {k} {l} {A} {B} F G =
  let module A = Precategory A in
  let module B = Precategory B in
  let module F = Functor F in
  let module G = Functor G in
    Σ[ α-ob ∈ ((x : A.ob) → B.hom (F.F-ob x) (G.F-ob x)) ] (
    {x y : A.ob} (f : A.hom x y) → B.comp (α-ob y) (F.F-hom f) ≡ B.comp (G.F-hom f) (α-ob x))

postulate
  Nat-trans-Sig-eq : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l}
                     (F G : Functor A B)
                     → Nat-trans-Sig F G ≡ Nat-trans F G

Nat-trans-sig→rec : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l}
                     (F G : Functor A B)
                     → Nat-trans-Sig F G → Nat-trans F G
Nat-trans.α-ob (Nat-trans-sig→rec F G (α₁ , α₂)) = α₁
Nat-trans.α-hom (Nat-trans-sig→rec F G (α₁ , α₂)) = α₂

Nat-trans-rec→sig : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l}
                       (F G : Functor A B)
                       → Nat-trans F G → Nat-trans-Sig F G
Nat-trans-rec→sig F G record { α-ob = α-ob ; α-hom = α-hom } =
  α-ob ,
  α-hom

NT-rec→sig→rec : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l}
                 (F G : Functor A B)
                 → (α : Nat-trans F G) → (Nat-trans-sig→rec F G o Nat-trans-rec→sig F G) α ≡ α
NT-rec→sig→rec F G α = refl

NT-sig→rec→sig : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l}
                 (F G : Functor A B)
                 → (α : Nat-trans-Sig F G) → (Nat-trans-rec→sig F G o Nat-trans-sig→rec F G) α ≡ α
NT-sig→rec→sig F G (a , b) = path-equiv-sigma
  (refl , refl)

NT-equiv-Sig : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l}
               (F G : Functor A B)
               → (Nat-trans-Sig F G) ≃ (Nat-trans F G)
NT-equiv-Sig F G = equiv-adjointify
  (Nat-trans-sig→rec F G ,
  (Nat-trans-rec→sig F G) ,
  (NT-rec→sig→rec F G) ,
  (NT-sig→rec→sig F G))







-- nat-trans-form-set : {i j k l : Level} {A : Precategory i j} {B : Precategory k l}
--                      (F G : Functor A B)
--                      → isSet (Nat-trans F G)
-- nat-trans-form-set {i} {j} {k} {l} {A} {B} F G =
--   let module A = Precategory A in
--   let module B = Precategory B in
--   let module F = Functor F in
--   let module G = Functor G in
--   transport (λ Z → isSet Z) (Nat-trans-Sig-eq F G)
--   (prop-fibres-totalspace-set (fibs-are-sets-PI-is-set λ x → B.hom-set _ _) λ {a x y →
--     Nat-trans.α-hom-is-prop {_} {_} {_} {_} {A} {B} {F} {G} (record { α-ob = a ; α-hom = λ f → y _ _ f}) x y)

lemma : ∀ {i} {A B : Type i}
        (x y : B) (F : A ≃ B)
        → pr₁ (pr₂ F) x ≡ pr₁ (pr₂ F) y → x ≡ y
lemma x y (f , g , η , ε , τ) p = ε x ^ ∘ (ap f p) ∘ ε y

open Nat-trans

nat-trans-id : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l}
               {F G : Functor A B} (α β : Nat-trans F G)
               → (Nat-trans.α-ob α ≡ Nat-trans.α-ob β) → α ≡ β
nat-trans-id {i} {j} {k} {l} {A} {B} {F} {G} α β p = lemma α β (NT-equiv-Sig F G)
  (fibres-props-eq
    (λ {T X Y → implicit-funext λ a → implicit-funext λ b → funextD λ f → Precategory.hom-set B _ _ _ _ _ _})
    ((α .α-ob) , (α .α-hom))
    ((β .α-ob) , (β .α-hom))
    p)



--   fibres-props-eq
--     (λ T X Y → funextD λ a → funextD λ b → funextD λ f → hom-set B _ _ _ _ _ _)
--     (α₁ , α₂)
--     (β₁ , β₂)
--     p







-- idⁿ : ∀ {i j k l} {A : Precategory {i} {j}} {B : Precategory {k} {l}} {F : functor A B}
--       → nat-trans {_} {_} {_} {_} {A} {B} F F
-- idⁿ {i} {j} {k} {l} {A} {B} {F} =
--   (λ x → Id B) ,
--   (λ x y f → r-Id B (F-hom {_} {_} {_} {_} {A} {B} F f) ∘ l-Id B (F-hom {_} {_} {_} {_} {A} {B} F f) ^  )

-- nat-trans-compᵛ : ∀ {i j k l} {A : Precategory {i} {j}} {B : Precategory {k} {l}} {F G H : functor A B}
--                   (β : nat-trans {_} {_} {_} {_} {A} {B} G H) (α : nat-trans {_} {_} {_} {_} {A} {B} F G)
--                   → nat-trans {_} {_} {_} {_} {A} {B} F H
-- nat-trans-compᵛ {i} {j} {k} {l} {A} {B} {F} {G} {H} (β₁ , β₂) (α₁ , α₂) =
--   (λ a → comp B (β₁ a) (α₁ a)) ,
--   λ a b f → transport (λ Z → comp B (comp B (β₁ b) (α₁ b)) (F-hom {_} {_} {_} {_} {A} {B} F f) ≡ comp B (Z) (α₁ a)) (β₂ a b f)
--     (ass B (F-hom {_} {_} {_} {_} {A} {B} F f) (α₁ b) (β₁ b) ^ ∘
--     ap (λ Z → comp B (β₁ b) Z)
--       (α₂ a b f)
--     ∘ ass B (α₁ a) (F-hom {_} {_} {_} {_} {A} {B} G f) (β₁ b))
--   ∘ ass B (α₁ a) (β₁ a) (F-hom {_} {_} {_} {_} {A} {B} H f) ^






-- nat-trans-id-compᵛ : ∀ {i j k l} {A : Precategory {i} {j}} {B : Precategory {k} {l}}
--                      (F G : functor A B) (α : nat-trans {_} {_} {_} {_} {A} {B} F G)
--                      → nat-trans-compᵛ {_} {_} {_} {_} {A} {B} {F} {G} {G} (idⁿ {_} {_} {_} {_} {A} {B} {G}) α ≡ α
-- nat-trans-id-compᵛ {i} {j} {k} {l} {A} {B} F G (α₁ , α₂) =
--   nat-trans-id {_} {_} {_} {_} {A} {B} {F} {G} _ _
--     (funextD λ a → r-Id B (α₁ a))

-- nat-trans-compᵛ-id : ∀ {i j k l} {A : Precategory {i} {j}} {B : Precategory {k} {l}}
--                      (F G : functor A B) (α : nat-trans {_} {_} {_} {_} {A} {B} F G)
--                      → nat-trans-compᵛ {_} {_} {_} {_} {A} {B} {F} {F} {G} α (idⁿ {_} {_} {_} {_} {A} {B} {F}) ≡ α
-- nat-trans-compᵛ-id {i} {j} {k} {l} {A} {B} F G (α₁ , α₂) =
--   nat-trans-id {_} {_} {_} {_} {A} {B} {F} {G} _ _
--     (funextD λ a → l-Id B (α₁ a))


-- nat-trans-comp-assoc : ∀ {i j k l} {A : Precategory {i} {j}} {B : Precategory {k} {l}} {F G H K : functor A B}
--                        (α : nat-trans {_} {_} {_} {_} {A} {B} F G) (β : nat-trans {_} {_} {_} {_} {A} {B} G H) (γ : nat-trans {_} {_} {_} {_} {A} {B} H K)
--                      → nat-trans-compᵛ {_} {_} {_} {_} {A} {B} {F} {H} {K} γ (nat-trans-compᵛ {_} {_} {_} {_} {A} {B} {F} {G} {H} β α) ≡ nat-trans-compᵛ {_} {_} {_} {_} {A} {B} {F} {G} {K} (nat-trans-compᵛ {_} {_} {_} {_} {A} {B} {G} {H} {K} γ β) α
-- nat-trans-comp-assoc {i} {j} {k} {l} {A} {B} {F} {G} {H} {K} (α₁ , α₂) (β₁ , β₂) (γ₁ , γ₂) =
--    nat-trans-id {_} {_} {_} {_} {A} {B} {F} {K} _ _
--      (funextD λ x → ass B (α₁ x) (β₁ x) (γ₁ x))


