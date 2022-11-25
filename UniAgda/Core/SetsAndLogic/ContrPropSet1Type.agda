{-# OPTIONS --without-K --safe --no-import-sorts #-}
module UniAgda.Core.SetsAndLogic.ContrPropSet1Type where

open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Identity
open import UniAgda.Core.Types.Sigma

-- * Definition
-- ** Contractible Types
-- A contractible type is one which has a point and a path from every
-- *other point to that point.
--  Definition3.11.1

isContr : ∀ {i}
          (A : Type i)
           → Type i
isContr A = Σ[ a ∈ A ] ((x : A) → a ≡ x)

-- ** Propositions
-- A proposition is a type with a path between any two terms.
--  Definition3.3.1

isProp : ∀ {i}
         (A : Type i)
         → Type i
isProp A = (x y : A) → x ≡ y

-- We define the type of propositions to be the Sigma type of types
-- that are propositions.

Prop_ : (i : Level)
        → Type (lsuc i)
Prop i =  Σ[ A ∈ Type i ] (isProp A)

-- ** Sets
-- A set is a type with all path spaces propositions.
--  Definition3.1.1

isSet : ∀ {i}
        (A : Type i)
        → Type i
isSet A = (x y : A) (p q : x ≡ y) → p ≡ q



sets-have-prop-ids : ∀ {i}
                     (A : Type i) → isSet A
                     → (x y : A) → isProp (x ≡ y)
sets-have-prop-ids A H x y = H x y

-- A set is then a type with a proof that it is a set. This is how we
-- define the type of sets.

Set_ : (i : Level)
       → Type (lsuc i)
Set_ i = Σ[ A ∈ Type i ] (isSet A)

-- ** 1-Types
-- We can extend this higher and we get a tower of \(n\)-types. We
-- just define 1-types here.
--  Definition3.1.7

is1type : ∀ {i}
          (A : Type i)
          → Type i
is1type A = (a b : A) → isSet (a ≡ b)
