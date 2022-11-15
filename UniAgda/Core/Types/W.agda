{-# OPTIONS --without-K --no-import-sorts --safe --no-import-sorts #-}
module UniAgda.Core.Types.W where

open import UniAgda.Core.Types.Universes

data W {i j : Level} (A : Type i) (B : A → Type j) : Type (i ⊔ j) where
  sup : (a : A) → (B a → W A B) → W A B

syntax W A (λ x → B) = W[ x ∈ A ] B
