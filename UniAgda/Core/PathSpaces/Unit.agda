{-# OPTIONS --without-K --safe --no-import-sorts #-}
module UniAgda.Core.PathSpaces.Unit where

open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Functions
open import UniAgda.Core.Types.Identity
open import UniAgda.Core.Types.Sigma
open import UniAgda.Core.Types.Unit

open import UniAgda.Core.Homotopy
open import UniAgda.Core.Equivalences

-- * Paths in the Unit Type

thm2-8-1i : (x y : Unit)
            → (x ≡ y) → Unit
thm2-8-1i x y p = tt

thm2-8-1ii : (x y : Unit)
            → Unit → (x ≡ y)
thm2-8-1ii tt tt X = refl

private
  hom₁-unit : (x y : Unit)
         → thm2-8-1i x y o thm2-8-1ii x y ~ id
  hom₁-unit tt tt tt = refl

  hom₂-unit : (x y : Unit)
         → thm2-8-1ii x y o thm2-8-1i x y ~ id
  hom₂-unit tt .tt refl = refl

thm2-8-1 : (x y : Unit)
           → (x ≡ y) ≃ Unit
thm2-8-1 x y = equiv-adjointify ((thm2-8-1i x y) , (thm2-8-1ii x y) , hom₁-unit x y , hom₂-unit x y)
