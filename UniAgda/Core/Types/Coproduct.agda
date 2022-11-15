{-# OPTIONS --without-K --no-import-sorts --safe --no-import-sorts #-}
module UniAgda.Core.Types.Coproduct where

open import UniAgda.Core.Types.Universes

-- The coproduct of two types is defined inductively by elements from
-- each type.
data _+_ {i j : Level} (A : Type i) (B : Type j) : Type (i ⊔ j) where
  inl : A → A + B
  inr : B → A + B

-- * Induction
coproduct-ind : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
             → (A → C) → (B → C)
             → A + B → C
coproduct-ind x x₁ (inl x₂) = x x₂
coproduct-ind x x₁ (inr x₂) = x₁ x₂

-- * Commutativity
-- The coproduct is commutative.
coprod-swap : ∀ {i j} {A : Type i} {B : Type j}
              → A + B → B + A
coprod-swap (inl x) = inr x
coprod-swap (inr x) = inl x
