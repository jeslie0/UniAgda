{-# OPTIONS --without-K --rewriting #-}
module UniAgda.HITs.proptrunc where

open import UniAgda.HITs.core public

postulate
  ∥_∥ : {i : Level} (A : Type i) → Type i
  ∣_∣ : {i : Level} {A : Type i}
         → A → ∥ A ∥

  Ptrunc-paths : {i : Level} {A : Type i} (x y : ∥ A ∥ ) → x ≡ y

  Ptrunc-rec : {i j : Level} {A : Type i} {B : Type j}
               → isProp B → (f : A → B)
               → ∥ A ∥ → B

  βPtrunc-rec : {i j : Level} {A : Type i} {B : Type j}
               → (X : isProp B) → (f : A → B) → (a : A)
               → (Ptrunc-rec X f ∣ a ∣) ↦ f a

{-# REWRITE βPtrunc-rec #-}

{- Properties -}
Ptrunc-is-prop : {i : Level}
                 (A : Type i)
                 → isProp (∥ A ∥)
Ptrunc-is-prop A x y = Ptrunc-paths x y

lemma3-9-1 : {i : Level} {P : Type i}
             → isProp P
             → P ≃ ∥ P ∥
lemma3-9-1 {i} {P} X = props-equiv X (Ptrunc-is-prop P) (∣_∣ {i} {P}) (Ptrunc-rec X (λ z → z))
