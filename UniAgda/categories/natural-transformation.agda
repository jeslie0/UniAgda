{-# OPTIONS --without-K #-}
module UniAgda.categories.natural-transformation where

open import UniAgda.categories.functor public

record nat-trans {i j k l} {A : Precategory {i} {j}} {B : Precategory {j} {k}} (F G : functor A B) : Type (i ⊔ j ⊔ k ⊔ l) where
  no-eta-equality
  field
    α-ob : (x : ob A) → hom B (F-ob F x) (F-ob G x)
    α-hom : {x y : ob A} (f : hom A x y) → comp B (α-ob y) (F-hom F f) ≡ comp B (F-hom G f) (α-ob x)

open nat-trans public
