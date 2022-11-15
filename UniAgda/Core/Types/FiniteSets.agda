{-# OPTIONS --without-K --no-import-sorts #-}
module UniAgda.Core.Types.FiniteSets where

open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Functions
open import UniAgda.Core.Types.Nat
open import UniAgda.Core.Types.Empty
open import UniAgda.Core.Types.Unit
open import UniAgda.Core.Types.Coproduct

-- We give the definition of the nth ordinal
Fin : ℕ → Type lzero
Fin zero = Empty
Fin (suc n) = Fin n + Unit

-- We will prove that these are sets in a different file.
