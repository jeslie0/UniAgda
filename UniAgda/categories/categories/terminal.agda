{-# OPTIONS --without-K #-}
module UniAgda.categories.categories.terminal where

open import UniAgda.categories.category public


𝟙 : Precategory {lzero} {lzero}
ob 𝟙 = Unit
hom 𝟙 a b = Unit → Unit
hom-set 𝟙 a b = equiv-with-set unit-equiv-unitTOunit unit-is-set
Id 𝟙 = id
comp 𝟙 f g a = (g o f) a
l-Id 𝟙 f = refl
r-Id 𝟙 f = refl
ass 𝟙 f g h = refl
