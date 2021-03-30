{-# OPTIONS --without-K  --no-import-sorts #-}
module UniAgda.experimental.exp4 where

open import UniAgda.Core.Everything public

record monoid {i : Level} : Type (lsuc i) where
  inductive
  field
    M : Type i
    _<>_ : M → M → M
    monoid-is-set : isSet M


