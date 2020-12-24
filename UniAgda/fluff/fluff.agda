{-# OPTIONS --without-K #-}
module UniAgda.fluff.fluff where

open import UniAgda.everything public

-- record magma {i} : Type (lsuc i) where
--   no-eta-equality
--   field
--     carrier : Type i
--     _·_ : carrier → carrier → carrier

-- open magma public

-- reflex : ∀ {i} (X : magma {i}) (Y : magma {i})
--          (a b : carrier X) → (a · b) ≡ (a · b)
-- reflex X a b = refl



UA-for-predicates : ∀ {i} (X X' : Type i) (pX : isProp X) (pX' : isProp X')
                    → (X ≃ X') ≃ ((X , pX) ≡ (X' , pX')) 
UA-for-predicates X X' pX pX' = ({!!} ^ᵉ) oₑ id-equiv-to-prop-on-type X X' isProp (λ A → isProp-is-prop A) pX pX'



-- univalenceweq : ∀{i} (X X' : Type i)
--                 → (X ≡ X') ≃ (X ≃ X')
-- univalenceweq X X' = univalence


