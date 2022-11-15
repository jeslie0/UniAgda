{-# OPTIONS --without-K --no-import-sorts --safe --no-import-sorts #-}
module UniAgda.Core.Types.Empty where

open import UniAgda.Core.Types.Universes

-- The empty type is an inductive type with no elements defined.
data Empty : Type lzero where

-- * Induction
-- The induction principle is defined as follows:
Empty-ind : ∀ {i} {A : Type i}
            → Empty → A
Empty-ind ()

-- * Negation
-- The empty type allows us to define logical negation.
¬ : ∀ {i}
    (A : Type i)
    → Type i
¬ A = A → Empty
infix 50 ¬
