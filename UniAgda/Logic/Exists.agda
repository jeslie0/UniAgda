{-# OPTIONS --without-K --rewriting --no-import-sorts #-}
module UniAgda.Logic.Exists where
open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Sigma
open import UniAgda.Core.Types.Coproduct

open import UniAgda.HITs.PropTrunc

-- Merely exists
∃ : ∀ {i j}
    (A : Type i) (B : A → Type j)
    → Type (i ⊔ j)
∃ A B = ∥ Σ[ x ∈ A ] B x ∥

syntax ∃ A (λ x → B) = ∃[ x ∈ A ] B

-- Merely or
_∨_ : ∀ {i j}
      (A : Type i) (B : Type j)
      → Type (i ⊔ j)
A ∨ B = ∥ A + B ∥
