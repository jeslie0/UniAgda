{-# OPTIONS --without-K --rewriting #-}
module UniAgda.HITs.core where

open import UniAgda.core.CORE public

postulate
  _↦_ : {i : Level} {A : Type i} → A → A → Type i
{-# BUILTIN REWRITE _↦_ #-}
