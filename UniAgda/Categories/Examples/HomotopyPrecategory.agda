{-# OPTIONS --without-K --rewriting --no-import-sorts #-}
module UniAgda.Categories.Examples.HomotopyPrecategory where


open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Functions
open import UniAgda.Core.Types.Identity

open import UniAgda.Core.SetsAndLogic.Sets
open import UniAgda.Core.SetsAndLogic.Props

open import UniAgda.Categories.Category

open import UniAgda.HITs.0truncation

-- * Definition
--  Example9.1.18

Homotopy-Precategory-of-Types : (i : Level) → Precategory (lsuc i) i
Precategory.ob (Homotopy-Precategory-of-Types i) = Type i
Precategory.hom (Homotopy-Precategory-of-Types i) X Y = ∥ (X → Y) ∥₀
Precategory.hom-set (Homotopy-Precategory-of-Types i) X Y = 0trunc-paths
Precategory.Id (Homotopy-Precategory-of-Types i) = ∣ id ∣₀
Precategory.comp (Homotopy-Precategory-of-Types i) =
  0trunc-ind
    (λ g → 0trunc-ind
      (λ f → ∣ g o f ∣₀)
      λ f → 0trunc-paths)
    λ g → func-of-sets-is-set (0trunc-paths)
Precategory.IdL (Homotopy-Precategory-of-Types i) =
  0trunc-ind
    (λ f → refl)
    (0trunc-ind
      (λ f → props-are-sets (0trunc-paths _ _))
      λ f → props-are-sets (isSet-is-prop _))
Precategory.IdR (Homotopy-Precategory-of-Types i) =
  0trunc-ind
    (λ f → refl)
    (0trunc-ind
      (λ f → props-are-sets (0trunc-paths _ _))
      λ f → props-are-sets (isSet-is-prop _))
Precategory.Assoc (Homotopy-Precategory-of-Types i) =
  0trunc-ind
    (λ f → 0trunc-ind
      (λ g → 0trunc-ind
        (λ h → refl)
        λ h → props-are-sets (0trunc-paths _ _))
      λ g → fibs-are-sets-PI-is-set
        λ x → props-are-sets (0trunc-paths _ _))
    λ f → fibs-are-sets-PI-is-set
      λ g → fibs-are-sets-PI-is-set
        λ h → props-are-sets (0trunc-paths _ _)
