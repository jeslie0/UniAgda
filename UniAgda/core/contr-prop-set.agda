{-# OPTIONS --without-K #-}
module UniAgda.core.contr-prop-set where

open import UniAgda.core.primitives public

-- Contractibility
isContr : {i : Level}
          (A : Type i)
           → Type i
isContr A = Σ[ a ∈ A ] ((x : A) → a ≡ x)

-- Propositions
isProp : {i : Level} (A : Type i)
         → Type i
isProp A = (x y : A) → x ≡ y

Prop_ : (i : Level)
        → Type (lsuc i)
Prop i =  Σ[ A ∈ Type i ] (isProp A)


-- Sets
isSet : {i : Level} (A : Type i)
        → Type i
isSet A = (x y : A) (p q : x ≡ y) → p ≡ q

Set_ : (i : Level)
       → Type (lsuc i)
Set_ i = Σ[ A ∈ Type i ] (isSet A)

-- 1-types
is1type : ∀ {i} (A : Type i)
          → Type i
is1type A = (a b : A) → isSet (a ≡ b)

