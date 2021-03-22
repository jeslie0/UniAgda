{-# OPTIONS --without-K #-}
module UniAgda.experimental.exp2 where

open import UniAgda.Core.Everything public

data Σ₄ {i j k l : Level} (A : Type i) (B : A → Type j) (C : (a : A) → B a → Type k) (D : (a : A) (b : B a) → C a b → Type l) : Type (i ⊔ j ⊔ k ⊔ l) where
  pair₄ : (a : A) (b : B a) (c : C a b) (d : D a b c) → Σ₄ A B C D

pr⁴₁ : ∀ {i j k l} {A : Type i} {B : A → Type j} {C : (a : A) → B a → Type k} {D : (a : A) (b : B a) → C a b → Type l}
     → Σ₄ A B C D → A
pr⁴₁ (pair₄ a b c d) = a

pr⁴₂ : ∀ {i j k l} {A : Type i} {B : A → Type j} {C : (a : A) → B a → Type k} {D : (a : A) (b : B a) → C a b → Type l}
     → (w : Σ₄ A B C D) → B (pr⁴₁ w)
pr⁴₂ (pair₄ a b c d) = b

pr⁴₃ : ∀ {i j k l} {A : Type i} {B : A → Type j} {C : (a : A) → B a → Type k} {D : (a : A) (b : B a) → C a b → Type l}
     → (w : Σ₄ A B C D) → C (pr⁴₁ w) (pr⁴₂ w)
pr⁴₃ (pair₄ a b c d) = c

pr⁴₄ : ∀ {i j k l} {A : Type i} {B : A → Type j} {C : (a : A) → B a → Type k} {D : (a : A) (b : B a) → C a b → Type l}
     → (w : Σ₄ A B C D) → D (pr⁴₁ w) (pr⁴₂ w) (pr⁴₃ w)
pr⁴₄ (pair₄ a b c d) = d


private
  variable
    i j k : Level

data Σ₃ (A : Type i) (B : A → Type j) (C : (x : A) → B x → Type k) : Type (i ⊔ j ⊔ k) where
  pair₃ : (x : A) → (y : B x) → C x y → Σ₃ A B C

pr³₁ : {A : Type i} {B : A → Type j} {C : (x : A) → B x → Type k}
       → Σ₃ A B C → A
pr³₁ (pair₃ x y x₁) = x

pr³₂ : {A : Type i} {B : A → Type j} {C : (x : A) → B x → Type k}
       → (w : Σ₃ A B C) → B (pr³₁ w)
pr³₂ (pair₃ x y x₁) = y


pr³₃ : {A : Type i} {B : A → Type j} {C : (x : A) → B x → Type k}
       → (w : Σ₃ A B C) → C (pr³₁ w) (pr³₂ w)
pr³₃ (pair₃ x y x₁) = x₁

