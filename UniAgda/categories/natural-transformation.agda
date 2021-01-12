{-# OPTIONS --without-K #-}
module UniAgda.categories.natural-transformation where

open import UniAgda.categories.functor public

-- record nat-trans {i j k l : Level} {A : Precategory {i} {j}} {B : Precategory {k} {l}} (F G : functor A B) : Type (i ⊔ j ⊔ k ⊔ l) where
--   pattern
--   field
--     α-ob : (x : ob A) → hom B (F-ob F x) (F-ob G x)
--     α-hom : {x y : ob A} (f : hom A x y) → comp B (α-ob y) (F-hom F f) ≡ comp B (F-hom G f) (α-ob x)

nat-trans : {i j k l : Level} {A : Precategory {i} {j}} {B : Precategory {k} {l}}
            (F G : functor A B)
            → Type (i ⊔ j ⊔ l)
nat-trans {i} {j} {k} {l} {A} {B} F G =
  Σ[ α-ob ∈ ((x : ob A) → hom B (F-ob {_} {_} {_} {_} {A} {B} F x) (F-ob {_} {_} {_} {_} {A} {B} G x)) ] (
    (x y : ob A) (f : hom A x y) → comp {_} {_} B (α-ob y) (F-hom {_} {_} {_} {_} {A} {B} F f) ≡ comp B (F-hom {_} {_} {_} {_} {A} {B} G f) (α-ob x))

α-ob : {i j k l : Level} {A : Precategory {i} {j}} {B : Precategory {k} {l}} {F G : functor A B}
       (α : nat-trans {_} {_} {_} {_} {A} {B} F G)
       → (x : ob A) → hom B (F-ob {_} {_} {_} {_} {A} {B} F x) (F-ob {_} {_} {_} {_} {A} {B} G x)
α-ob {i} {j} {k} {l} {A} {B} {F} {G} (a , b) = a

α-hom : {i j k l : Level} {A : Precategory {i} {j}} {B : Precategory {k} {l}} {F G : functor A B}
        (α : nat-trans {_} {_} {_} {_} {A} {B} F G)
        → (x y : ob A) (f : hom A x y) → comp B (α-ob {_} {_} {_} {_} {A} {B} {F} {G} α y) (F-hom {_} {_} {_} {_} {A} {B} F f) ≡ comp B (F-hom {_} {_} {_} {_} {A} {B} G f) (α-ob {_} {_} {_} {_} {A} {B} {F} {G} α x)
α-hom (a , b) = b


nat-trans-id : ∀ {i j k l} {A : Precategory {i} {j}} {B : Precategory {k} {l}}
               {F G : functor A B} (α β : nat-trans {_} {_} {_} {_} {A} {B} F G)
               → (α-ob {_} {_} {_} {_} {A} {B} {F} {G} α ≡ α-ob {_} {_} {_} {_} {A} {B} {F} {G} β) → α ≡ β
nat-trans-id {i} {j} {k} {l} {A} {B} {F} {G} (α₁ , α₂) (β₁ , β₂) p =
  fibres-props-eq
    (λ T X Y → funextD λ a → funextD λ b → funextD λ f → hom-set B _ _ _ _ _ _)
    (α₁ , α₂)
    (β₁ , β₂)
    p



α-hom-is-prop : {i j k l : Level} {A : Precategory {i} {j}} {B : Precategory {k} {l}} {F G : functor A B}
                (α : nat-trans {_} {_} {_} {_} {A} {B} F G) 
                → isProp ((x y : ob A) (f : hom A x y) → comp B (α-ob {_} {_} {_} {_} {A} {B} {F} {G} α y) (F-hom {_} {_} {_} {_} {A} {B} F f) ≡ comp B (F-hom {_} {_} {_} {_} {A} {B} G f) (α-ob {_} {_} {_} {_} {A} {B} {F} {G} α x))
α-hom-is-prop {i} {j} {k} {l} {A} {B} {F} {G} α f g =
  funextD λ a → funextD λ b → funextD λ x → hom-set B _ _ _ _ _ _


nat-trans-form-set : {i j k l : Level} {A : Precategory {i} {j}} {B : Precategory {k} {l}}
                     (F G : functor A B)
                     → isSet (nat-trans {_} {_} {_} {_} {A} {B} F G)
nat-trans-form-set {i} {j} {k} {l} {A} {B} F G = prop-fibres-totalspace-set (fibs-are-sets-PI-is-set (λ x → hom-set B _ _)) λ a → λ x y → α-hom-is-prop {_} {_} {_} {_} {A} {B} {F} {G} (a , y) x y


idⁿ : ∀ {i j k l} {A : Precategory {i} {j}} {B : Precategory {k} {l}} {F : functor A B}
      → nat-trans {_} {_} {_} {_} {A} {B} F F
idⁿ {i} {j} {k} {l} {A} {B} {F} =
  (λ x → Id B) ,
  (λ x y f → r-Id B (F-hom {_} {_} {_} {_} {A} {B} F f) ∘ l-Id B (F-hom {_} {_} {_} {_} {A} {B} F f) ^  )

nat-trans-compᵛ : ∀ {i j k l} {A : Precategory {i} {j}} {B : Precategory {k} {l}} {F G H : functor A B}
                  (β : nat-trans {_} {_} {_} {_} {A} {B} G H) (α : nat-trans {_} {_} {_} {_} {A} {B} F G)
                  → nat-trans {_} {_} {_} {_} {A} {B} F H
nat-trans-compᵛ {i} {j} {k} {l} {A} {B} {F} {G} {H} (β₁ , β₂) (α₁ , α₂) =
  (λ a → comp B (β₁ a) (α₁ a)) ,
  λ a b f → transport (λ Z → comp B (comp B (β₁ b) (α₁ b)) (F-hom {_} {_} {_} {_} {A} {B} F f) ≡ comp B (Z) (α₁ a)) (β₂ a b f)
    (ass B (F-hom {_} {_} {_} {_} {A} {B} F f) (α₁ b) (β₁ b) ^ ∘
    ap (λ Z → comp B (β₁ b) Z)
      (α₂ a b f)
    ∘ ass B (α₁ a) (F-hom {_} {_} {_} {_} {A} {B} G f) (β₁ b))
  ∘ ass B (α₁ a) (β₁ a) (F-hom {_} {_} {_} {_} {A} {B} H f) ^






nat-trans-id-compᵛ : ∀ {i j k l} {A : Precategory {i} {j}} {B : Precategory {k} {l}}
                     (F G : functor A B) (α : nat-trans {_} {_} {_} {_} {A} {B} F G)
                     → nat-trans-compᵛ {_} {_} {_} {_} {A} {B} {F} {G} {G} (idⁿ {_} {_} {_} {_} {A} {B} {G}) α ≡ α
nat-trans-id-compᵛ {i} {j} {k} {l} {A} {B} F G (α₁ , α₂) =
  nat-trans-id {_} {_} {_} {_} {A} {B} {F} {G} _ _
    (funextD λ a → r-Id B (α₁ a))

nat-trans-compᵛ-id : ∀ {i j k l} {A : Precategory {i} {j}} {B : Precategory {k} {l}}
                     (F G : functor A B) (α : nat-trans {_} {_} {_} {_} {A} {B} F G)
                     → nat-trans-compᵛ {_} {_} {_} {_} {A} {B} {F} {F} {G} α (idⁿ {_} {_} {_} {_} {A} {B} {F}) ≡ α
nat-trans-compᵛ-id {i} {j} {k} {l} {A} {B} F G (α₁ , α₂) =
  nat-trans-id {_} {_} {_} {_} {A} {B} {F} {G} _ _
    (funextD λ a → l-Id B (α₁ a))


nat-trans-comp-assoc : ∀ {i j k l} {A : Precategory {i} {j}} {B : Precategory {k} {l}} {F G H K : functor A B}
                       (α : nat-trans {_} {_} {_} {_} {A} {B} F G) (β : nat-trans {_} {_} {_} {_} {A} {B} G H) (γ : nat-trans {_} {_} {_} {_} {A} {B} H K)
                     → nat-trans-compᵛ {_} {_} {_} {_} {A} {B} {F} {H} {K} γ (nat-trans-compᵛ {_} {_} {_} {_} {A} {B} {F} {G} {H} β α) ≡ nat-trans-compᵛ {_} {_} {_} {_} {A} {B} {F} {G} {K} (nat-trans-compᵛ {_} {_} {_} {_} {A} {B} {G} {H} {K} γ β) α
nat-trans-comp-assoc {i} {j} {k} {l} {A} {B} {F} {G} {H} {K} (α₁ , α₂) (β₁ , β₂) (γ₁ , γ₂) =
   nat-trans-id {_} {_} {_} {_} {A} {B} {F} {K} _ _
     (funextD λ x → ass B (α₁ x) (β₁ x) (γ₁ x))


