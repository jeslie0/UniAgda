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
module ≡-Reasoning {i : Level} {A : Type i} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A}
    → x ≡ y
      -----
    → x ≡ y
  begin x≡y  =  x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≡ y
      -----
    → x ≡ y
  x ≡⟨⟩ x≡y  =  x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
      -----
    → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z  =  _∘_ x≡y y≡z

  _∎ : ∀ (x : A)
      -----
    → x ≡ x
  x ∎  =  refl

open ≡-Reasoning

trans : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
  --------
  → x ≡ z
trans {A} {x} {y} {z} p q =
  begin
      x
    ≡⟨ p ⟩
      y
    ≡⟨ q ⟩
      z
    ∎
