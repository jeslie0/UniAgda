{-# OPTIONS --without-K --no-import-sorts --safe --no-import-sorts #-}
module UniAgda.Core.Types.Bool where

open import UniAgda.Core.Types.Universes

-- The type of Booleans is inductively defined by two terms that we
-- call "true" and "false".

data Bool : Type lzero where
  true : Bool
  false : Bool

{-# BUILTIN BOOL Bool #-}
{-# BUILTIN TRUE true #-}
{-# BUILTIN FALSE false #-}

-- We also define the "swap" function, which permutes the values of
-- "true" and "false".
swap : Bool → Bool
swap true = false
swap false = true
