{-# OPTIONS --without-K --rewriting #-}
module UniAgda.logic.exists where
open import UniAgda.core.CORE public
open import UniAgda.HITs.proptrunc public

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
