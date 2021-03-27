{-# OPTIONS --without-K --rewriting --no-import-sorts #-}
module UniAgda.experimental.exp3 where

open import UniAgda.Core.Everything public
open import UniAgda.Equiv.Inj-Surj

open import UniAgda.HITs.Core

postulate
  _/_ : ∀ {i j}
        (A : Type i) (R : (A × A) → Prop_ j)
        → Type j
  quotient-map : ∀ {i j} {A : Type i}
                 (R : (A × A) → Prop_ j)
                 → (A → A / R)
  quotient-eq : {i j : Level} {A : Type i} {R : (A × A) → Prop_ j}
                (a b : A) → pr₁ (R (a , b))
                → (quotient-map R a) ≡ (quotient-map R b)
  quotient-set : {i j : Level} {A : Type i} {R : (A × A) → Prop_ j}
                 → isSet (A / R)

-- postulate
--   quotient-rec : ∀ {i j} 


quotient-map-is-surj : ∀ {i j} {A : Type i} {R : A × A → Prop_ j}
                       → isSurj (quotient-map R)
quotient-map-is-surj x =
  ∣ {!!} , {!!} ∣
    where a = {!!}
