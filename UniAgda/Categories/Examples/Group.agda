{-# OPTIONS --without-K  --no-import-sorts #-}
module UniAgda.Categories.Examples.Group where

open import UniAgda.Core.Types.Universes

open import UniAgda.Categories.Category
open import UniAgda.Algebra.GroupTheory.basics
open Precategory

-- * Category of groups

GROUP : (i : Level) → Precategory (lsuc i) i
ob (GROUP i) = Group i
hom (GROUP i) = Group-hom {i} {i}
hom-set (GROUP i) G H = Group-hom-is-set
Id (GROUP i) = Idᵍ
comp (GROUP i) = ghom-comp
IdL (GROUP i) = ghom-lId
IdR (GROUP i) = ghom-rId
Assoc (GROUP i) = ghom-assoc
