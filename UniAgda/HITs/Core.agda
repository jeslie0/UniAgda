{-# OPTIONS --without-K --rewriting #-}
module UniAgda.HITs.Core where

open import UniAgda.Core.Types.Universes

postulate
  _↦_ : {i : Level} {A : Type i} → A → A → Type i
{-# BUILTIN REWRITE _↦_ #-}
