{-# OPTIONS --without-K --no-import-sorts --safe --no-import-sorts #-}
module UniAgda.Core.Types.Sigma where

open import UniAgda.Core.Types.Universes
-- We define the dependant pair inductively, rather than as a record.
data Σ {i j : Level} (A : Type i) (B : A → Type j) : Type (i ⊔ j) where
  _,_ : (a : A) → (b : B a) → Σ A B

syntax Σ A (λ x → B) = Σ[ x ∈ A ] B
infixr 4 _,_
infixr 4 Σ

-- They come with projection functions for each component:
pr₁ : ∀ {i j} {A : Type i} {B : A → Type j}
      → Σ A B
      → A
pr₁ (a , b) = a

pr₂ : ∀ {i j} {A : Type i} {B : A → Type j}
      (w : Σ A B)
      → B (pr₁ w)
pr₂ (a , b) = b

-- *Product Types
-- We define product types to be a special case of Sigma types,
-- meaning we can apply results about Sigma types straight to product
-- types.
_×_ : ∀ {i j}
      (A : Type i) (B : Type j)
      → Type (i ⊔ j)
A × B = Σ A (λ _ → B)
infixr 4 _×_

-- * If and only if
-- We can define if and only if using product types.
_↔_ : ∀ {i j} (A : Type i) (B : Type j) → Type (i ⊔ j)
A ↔ B = (A → B) × (B → A)
