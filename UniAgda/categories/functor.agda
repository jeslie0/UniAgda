{-# OPTIONS --without-K #-}
module UniAgda.categories.functor where

open import UniAgda.categories.precategory public


record functor {i j k l} (A : Precategory {i} {j}) (B : Precategory {k} {l}) : Type (i ⊔ j ⊔ k ⊔ l) where
  no-eta-equality
  field
    F-ob : ob A → ob B
    F-hom : {a b : ob A} → hom A a b → hom B (F-ob a) (F-ob b)
    F-id : {a : ob A} → F-hom (Id A {a}) ≡ (Id B {F-ob a})
    F-nat : {a b c : ob A} (g : hom A b c) (f : hom A a b) → F-hom (comp A g f) ≡ comp B (F-hom g) (F-hom f)

open functor public
