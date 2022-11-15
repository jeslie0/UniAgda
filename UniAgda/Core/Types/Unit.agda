{-# OPTIONS --without-K --no-import-sorts --safe --no-import-sorts #-}
module UniAgda.Core.Types.Unit where

open import UniAgda.Core.Types.Universes

-- The unit type is an inductive type with only one term defined.

data Unit : Type lzero where
  tt : Unit
