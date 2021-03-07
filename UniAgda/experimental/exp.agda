{-# OPTIONS --without-K #-}
module UniAgda.experimental.exp where
open import UniAgda.core.CORE public

contrapos1 : ∀ {i j} {A : Type i} {B : Type j}
            → (A → B)
            → (¬ B → ¬ A)
contrapos1 f x₁ x₂ = x₁ (f x₂)

contrapos2 : ∀ {i j} {A : Type i} {B : Type j}
            → (¬ B → ¬ A)
            → (A → ¬ (¬ B))
contrapos2 f a x = f x a


-- lemma : ∀ {i j k} {A : Type i} {B : A → Type j} {C : (a : A) → B a → Type k}
--         → ((a : A) → (b : B a) → isProp (C a b)) → (X Y : Σ[ a ∈ A ] (Σ[ b ∈ (B a)] (C a b)))
--         → ((pr₁ X) , (pr₁ (pr₂ X))) ≡ ((pr₁ Y) , (pr₁ (pr₂ Y))) → X ≡ Y
-- lemma x X Y p = {!!}

open import UniAgda.categories.category
open import UniAgda.categories.functor
open import UniAgda.categories.natural-transformation


record Monad {i j : Level} (C : Precategory i j) : Type (lsuc (i ⊔ j)) where
  field
    F : Functor C C
    η : NaturalTransformation Idᶠ F
    μ : NaturalTransformation (compᶠ F F) F

  module F = Functor F
  module η = NaturalTransformation η
  module μ = NaturalTransformation μ

lemma : power 3 2 ≡ 9
lemma = refl

ℤ : Type lzero
ℤ = ℕ + ℕ

pre : ℤ → ℤ
pre (inl zero) = inl (suc zero)
pre (inl (suc x)) = inl x
pre (inr zero) = inl zero
pre (inr (suc x)) = inr x


ℤplus : ℤ → ℤ → ℤ
ℤplus (inl x) (inl y) = inl (plus x y)
ℤplus (inl zero) (inr y) = inr y
ℤplus (inl (suc x)) (inr y) = {!!}
ℤplus (inr x) (inl y) = {!!}
ℤplus (inr x) (inr y) = inr (plus x y)

