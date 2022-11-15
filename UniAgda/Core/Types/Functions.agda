{-# OPTIONS --without-K --no-import-sorts --safe --no-import-sorts #-}
module UniAgda.Core.Types.Functions where

open import UniAgda.Core.Types.Universes

-- Agda introduces most of the required function types already. This
-- means we don't need to define Π types or → types, just
-- their basic operations.
_o_ : ∀ {i₁ i₂ i₃} {A : Type i₁} {B : Type i₂} {C : Type i₃}
      (g : B → C) (f : A → B)
      → A → C
(g o f) a = g (f a)
infixr 9 _o_

id : ∀ {i} {A : Type i}
     → A → A
id a = a

-- We introduce Haskell notation for function application.
_$_ : ∀ {i j} {A : Type i} {B : Type j}
     → (A → B) → A → B
f $ a = f a
infixr 0 _$_
