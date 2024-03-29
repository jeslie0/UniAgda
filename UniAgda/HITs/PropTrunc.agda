{-# OPTIONS --without-K --rewriting --no-import-sorts #-}
module UniAgda.HITs.PropTrunc where

open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Identity

open import UniAgda.Core.SetsAndLogic.ContrPropSet1Type
open import UniAgda.Core.SetsAndLogic.Props
open import UniAgda.Core.Equivalences
open import UniAgda.HITs.Core

postulate
  ∥_∥ : {i : Level} (A : Type i) → Type i
  ∣_∣ : {i : Level} {A : Type i}
         → A → ∥ A ∥

  prop-trunc-paths : {i : Level} {A : Type i} (x y : ∥ A ∥ ) → x ≡ y

  prop-trunc-rec : {i j : Level} {A : Type i} {B : Type j}
               → isProp B → (f : A → B)
               → ∥ A ∥ → B

  βprop-trunc-rec : {i j : Level} {A : Type i} {B : Type j}
               → (X : isProp B) → (f : A → B) → (a : A)
               → (prop-trunc-rec X f ∣ a ∣) ↦ f a

{-# REWRITE βprop-trunc-rec #-}





{- Properties -}
prop-trunc-is-prop : {i : Level}
                 (A : Type i)
                 → isProp (∥ A ∥)
prop-trunc-is-prop A x y = prop-trunc-paths x y

lemma3-9-1 : {i : Level} {P : Type i}
             → isProp P
             → P ≃ ∥ P ∥
lemma3-9-1 {i} {P} X = props-equiv X (prop-trunc-is-prop P) (∣_∣ {i} {P}) (prop-trunc-rec X (λ z → z))



prop-trunc-ind : ∀ {i j} {A : Type i} {B : ∥ A ∥ → Type j}
                 → ((x : ∥ A ∥) → isProp (B x))
                 → ((a : A) → B (∣ a ∣))
                 → (x : ∥ A ∥) → B x
prop-trunc-ind {A = A} {B = B} F f x =
  prop-trunc-rec
    (F x)
    (λ a → transport B (prop-trunc-is-prop (A) ∣ a ∣ x) (f a))
    x
