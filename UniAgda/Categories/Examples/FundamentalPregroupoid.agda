{-# OPTIONS --without-K --rewriting --no-import-sorts #-}
module UniAgda.Categories.Examples.FundamentalPregroupoid where

open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Identity

open import UniAgda.Core.PathAlgebra

open import UniAgda.Core.SetsAndLogic.Sets
open import UniAgda.Core.SetsAndLogic.Props

open import UniAgda.Categories.Category

open import UniAgda.HITs.0truncation
private
  variable
    i j : Level

-- * Definition
--  Example9.1.17

fundamental-pregroupoid : (X : Type i) → Precategory i i
Precategory.ob (fundamental-pregroupoid X) = ∥ X ∥₀
Precategory.hom (fundamental-pregroupoid X) x y = ∥ x ≡ y ∥₀
Precategory.hom-set (fundamental-pregroupoid X) x y = 0trunc-paths
Precategory.Id (fundamental-pregroupoid X) = ∣ refl ∣₀
Precategory.comp (fundamental-pregroupoid X) p' q' =
  0trunc-ind
    (λ p → 0trunc-ind
         (λ q → ∣ q ∘ p ∣₀)
         (λ x → 0trunc-paths)
         q')
    (λ x → 0trunc-paths)
    p'
Precategory.IdL (fundamental-pregroupoid X) =
  0trunc-ind
    (λ p → refl)
    λ p → props-are-sets (0trunc-paths _ _)
Precategory.IdR (fundamental-pregroupoid X) =
  0trunc-ind
    (λ p → ap ∣_∣₀ (p-refl p))
    λ p → props-are-sets (0trunc-paths _ _)
Precategory.Assoc (fundamental-pregroupoid X) =
  0trunc-ind
    (λ p → 0trunc-ind
      (λ q → 0trunc-ind
        (λ r → ap ∣_∣₀ (ass-l p q r))
        λ r → props-are-sets (0trunc-paths _ _))
      λ q → fibs-are-sets-PI-is-set
        λ r → props-are-sets (0trunc-paths _ _))
    λ p → fibs-are-sets-PI-is-set
      λ q → fibs-are-sets-PI-is-set
        λ r → props-are-sets (0trunc-paths _ _)
