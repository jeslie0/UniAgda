{-# OPTIONS --without-K --safe --no-import-sorts #-}
module UniAgda.Core.Types.Nat where

open import UniAgda.Core.Types.Universes
-- * The Natural Numbers
-- The natural numbers are defined inductively by zero and the
-- successor function.
data ℕ  : Type lzero where
  zero : ℕ
  suc : ℕ -> ℕ
{-# BUILTIN NATURAL ℕ #-}

-- * Addition, subtraction, multiplication and exponentiation
-- The standard functions on \(\mathbb N\) are defined recursively.
plus : ℕ → ℕ → ℕ
plus zero m = m
plus (suc n) m = suc (plus n m)
{-# BUILTIN NATPLUS plus #-}

minus : ℕ → ℕ → ℕ
minus n zero = n
minus zero (suc m) = zero
minus (suc n) (suc m) = minus n m
{-# BUILTIN NATMINUS minus #-}

times : ℕ → ℕ → ℕ
times zero m = zero
times (suc n) m = plus (times n m) m
{-# BUILTIN NATTIMES times #-}

power : ℕ → ℕ → ℕ
power n zero = suc zero
power n (suc m) = times (power n m) n
