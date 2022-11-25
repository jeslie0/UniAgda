{-# OPTIONS --without-K  --no-import-sorts #-}
module UniAgda.Categories.Examples.Terminal where

open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Identity
open import UniAgda.Core.Types.Unit
open import UniAgda.Core.Types.Sigma

open import UniAgda.Core.PathSpaces.Sigma
open import UniAgda.Core.Equivalences

open import UniAgda.Core.SetsAndLogic.Sets
open import UniAgda.Core.SetsAndLogic.Equivalences

open import UniAgda.Categories.Category
open Precategory
open Category

-- * Definition
-- The terminal precategory has one object and the sole identity map.

𝟙 : Precategory lzero lzero
ob 𝟙 = Unit
hom 𝟙 a b = Unit
hom-set 𝟙 a b = Unit-is-set
Id 𝟙 {a} = a
comp 𝟙 f g = tt
IdL 𝟙 tt = refl
IdR 𝟙 tt = refl
Assoc 𝟙 f g h = refl

-- It is, of course, also a category.

𝟙-is-category : isCategory 𝟙
𝟙-is-category tt tt =
  isequiv-adjointify
    ((λ { (tt , tt , a , b) → refl}) ,
    (λ { (tt , tt , a , b) →
      path-equiv-sigma (refl ,
        (path-equiv-sigma (refl ,
          (path-equiv-sigma (Unit-is-set tt tt refl a ,
            Unit-is-set tt tt _ b)))))}) ,
    λ x → Unit-is-set tt tt _ x)
