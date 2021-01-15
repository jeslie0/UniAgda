{-# OPTIONS --without-K  #-}
module UniAgda.categories.functor where

open import UniAgda.categories.precat public


-- record functor {i j k l} (A : Precategory {i} {j}) (B : Precategory {k} {l}) : Type (i ⊔ j ⊔ k ⊔ l) where
--   no-eta-equality
--   field
--     F-ob : ob A → ob B
--     F-hom : {a b : ob A} → hom A a b → hom B (F-ob a) (F-ob b)
--     F-id : {a : ob A} → F-hom (Id A {a}) ≡ (Id B {F-ob a})
--     F-nat : {a b c : ob A} (g : hom A b c) (f : hom A a b) → F-hom (comp A g f) ≡ comp B (F-hom g) (F-hom f)

-- open functor public

functor : ∀ {i j k l}
          (A : Precategory {i} {j}) (B : Precategory {k} {l})
          → Type (i ⊔ j ⊔ k ⊔ l)
functor {i} {j} {k} {l} A B =
  Σ[ F-ob ∈ ((ob A) → (ob B))] (
       Σ[ F-hom ∈ ({a b : ob A} → hom A a b → hom B (F-ob a) (F-ob b))] (
         Σ[ F-id ∈ ({a : ob A} → F-hom (Id A {a}) ≡ (Id B {F-ob a}))] (
           ({a b c : ob A} (g : hom A b c) (f : hom A a b) → F-hom (comp A g f) ≡ comp B (F-hom g) (F-hom f)))))

F-ob : ∀ {i j k l} {A : Precategory {i} {j}} {B : Precategory {k} {l}}
       (F : functor A B)
       → (ob A) → (ob B)
F-ob (a , a₁ , a₂ , b) = a

F-hom : ∀ {i j k l} {A : Precategory {i} {j}} {B : Precategory {k} {l}}
       (F : functor A B)
       → {a b : ob A} → hom A a b → hom B (F-ob {_} {_} {_} {_} {A} {B} F a) (F-ob {_} {_} {_} {_} {A} {B} F b)
F-hom {i} {j} {k} {l} {A} {B} (a , a₁ , a₂ , b) = a₁

F-id : ∀ {i j k l} {A : Precategory {i} {j}} {B : Precategory {k} {l}}
       (F : functor A B)
       → {a : ob A} → F-hom {_} {_} {_} {_} {A} {B} F (Id A {a}) ≡ (Id B {F-ob {_} {_} {_} {_} {A} {B} F a})
F-id (a , a₁ , a₂ , b) = a₂

F-nat : ∀ {i j k l} {A : Precategory {i} {j}} {B : Precategory {k} {l}}
        (F : functor A B)
        → {a b c : ob A} (g : hom A b c) (f : hom A a b) → F-hom {_} {_} {_} {_} {A} {B} F (comp A g f) ≡ comp B (F-hom {_} {_} {_} {_} {A} {B} F g) (F-hom {_} {_} {_} {_} {A} {B} F f)
F-nat (a , a₁ , a₂ , b) = b



{- Functor composition -}

{- Identity functor -}
Idᶠ : ∀ {i j} {C : Precategory {i} {j}}
      → functor {_} {_} {_} {_} C C
Idᶠ {i} {j} {C} =
  id ,
  id ,
  refl ,
  (λ g f → refl)
