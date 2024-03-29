{-# OPTIONS --without-K --rewriting --no-import-sorts #-}
module UniAgda.HITs.0truncation where

open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Identity

open import UniAgda.Core.SetsAndLogic.ContrPropSet1Type
open import UniAgda.Core.SetsAndLogic.Props
open import UniAgda.Core.Equivalences
open import UniAgda.HITs.Core

private
  variable
    i j : Level



-- * Definition
-- We mostly use Lemma 6.9.1 to define the 0 truncation of a type,
-- rather than the formal induction principle defined before it in the
-- book. I haven't checked to see if they are equivalent, but
-- hopefully they are. The one we use is easier to use in practice
-- though.
--  Lemma6.9.1

postulate
  ∥_∥₀ : (A : Type i) → Type i
  ∣_∣₀ : {A : Type i} → A → ∥ A ∥₀
  0trunc-paths : {A : Type i} (x y : ∥ A ∥₀) (p q : x ≡ y) → p ≡ q

postulate
  0trunc-rec : {A : Type i} {B : Type j}
               → isSet B → (f : A → B)
               → ∥ A ∥₀ → B

  β0trunc-rec : {A : Type i} {B : Type j}
               → (X : isSet B) → (f : A → B) → (a : A)
               → (0trunc-rec X f ∣ a ∣₀) ↦ f a

{-# REWRITE β0trunc-rec #-}

postulate
  0trunc-ind : {A : Type i} {B : ∥ A ∥₀ → Type j}
               (g : (a : A) → B (∣ a ∣₀))
               → ((x : ∥ A ∥₀) → isSet (B x))
               → ((x : ∥ A ∥₀) → B x)

  β0trunc-ind : {A : Type i} {B : ∥ A ∥₀ → Type j}
                (a : A)
                (g : (a : A) → B (∣ a ∣₀))
                → (f : (x : ∥ A ∥₀) → isSet (B x))
                → 0trunc-ind g f (∣ a ∣₀) ↦ g a

{-# REWRITE β0trunc-ind #-}


-- * Misc

-- postulate
--   0trunc-ind : {A : Type i} {B : ∥ A ∥₀ → Type j}
--                (g : (a : A) → B(∣ a ∣₀))
--                (P : (x y : ∥ A ∥₀) (z : B x) (w : B y) (p q : x ≡ y) (r : transport B p z ≡ w) (s : transport B q z ≡ w) → r ≡ transport² (0trunc-paths x y p q) z ∘ s)
--                → ((x : ∥ A ∥₀) → B x)

  -- β0trunc-ind : {A : Type i} {B : ∥ A ∥₀ → Type j}
  --               (a : A)
  --               (g : (a : A) → B(∣ a ∣₀))
  --               (P : (x y : ∥ A ∥₀) (z : B x) (w : B y) (p q : x ≡ y) (r : transport B p z ≡ w) (s : transport B q z ≡ w) → r ≡ transport² (0trunc-paths x y p q) z ∘ s)
  --              → 0trunc-ind g P (∣ a ∣₀) ↦ g (a)

-- {-# REWRITE β0trunc-ind #-}
