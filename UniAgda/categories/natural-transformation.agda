{-# OPTIONS --without-K #-}
module UniAgda.categories.natural-transformation where

open import UniAgda.categories.functor public

-- record nat-trans {i j k l : Level} {A : Precategory {i} {j}} {B : Precategory {k} {l}} (F G : functor A B) : Type (i ⊔ j ⊔ k ⊔ l) where
--   pattern
--   field
--     α-ob : (x : ob A) → hom B (F-ob F x) (F-ob G x)
--     α-hom : {x y : ob A} (f : hom A x y) → comp B (α-ob y) (F-hom F f) ≡ comp B (F-hom G f) (α-ob x)

nat-trans : {i j k l : Level} {A : Precategory {i} {j}} {B : Precategory {k} {l}} (F G : functor A B) → Type (_)
nat-trans {i} {j} {k} {l} {A} {B} F G =
  Σ[ α-ob ∈ ((x : ob A) → hom B (F-ob {_} {_} {_} {_} {A} {B} F x) (F-ob {_} {_} {_} {_} {A} {B} G x)) ] (
    {x y : ob A} (f : hom A x y) → comp {_} {_} B (α-ob y) (F-hom {_} {_} {_} {_} {A} {B} F f) ≡ comp B (F-hom {_} {_} {_} {_} {A} {B} G f) (α-ob x))
-- Σ[ α-ob ∈ ((x : ob A) → hom B (F-ob F x) (F-ob G x)) ] ({x y : ob A} (f : hom A x y) → comp B (α-ob y) (F-hom F f) ≡ comp B (F-hom G f) (α-ob x))

α-ob : {i j k l : Level} {A : Precategory {i} {j}} {B : Precategory {k} {l}} {F G : functor A B} (α : nat-trans {_} {_} {_} {_} {A} {B} F G) → (x : ob A) → hom B (F-ob {_} {_} {_} {_} {A} {B} F x) (F-ob {_} {_} {_} {_} {A} {B} G x)
α-ob {i} {j} {k} {l} {A} {B} {F} {G} (a , b) = a

α-hom : {i j k l : Level} {A : Precategory {i} {j}} {B : Precategory {k} {l}} {F G : functor A B} (α : nat-trans {_} {_} {_} {_} {A} {B} F G)
        → {x y : ob A} (f : hom A x y) → comp B (α-ob {_} {_} {_} {_} {A} {B} {F} {G} α y) (F-hom {_} {_} {_} {_} {A} {B} F f) ≡ comp B (F-hom {_} {_} {_} {_} {A} {B} G f) (α-ob {_} {_} {_} {_} {A} {B} {F} {G} α x)
α-hom (a , b) = b


-- nat-trans-form-set : {i j k l : Level} {A : Precategory {i} {j}} {B : Precategory {j} {k}} {F G : functor A B}
--                      → isSet (nat-trans {_} {_} {_} {_} {A} {B} F G)
-- nat-trans-form-set (a , b) (a₁ , b₁) = {!path!}
