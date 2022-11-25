{-# OPTIONS --without-K  --no-import-sorts #-}
module UniAgda.Categories.Examples.Initial where

open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Empty

open import UniAgda.Categories.Category
open Precategory
open Category
-- * Definition
-- The initial precategory is a category with no objects. It is
-- defined as follows.
𝟘 : Precategory lzero lzero
ob 𝟘 = Empty
hom 𝟘 () b
hom-set 𝟘 () b
Id 𝟘 {()}
comp 𝟘 {()} f g
IdL 𝟘 {()} f
IdR 𝟘 {()} f
Assoc 𝟘 {()} f g h

-- It is immediate that it is a category.
𝟘-is-category : isCategory 𝟘
𝟘-is-category () b

𝟘-Cat : Category lzero lzero
∁ 𝟘-Cat = 𝟘
univ 𝟘-Cat = 𝟘-is-category
