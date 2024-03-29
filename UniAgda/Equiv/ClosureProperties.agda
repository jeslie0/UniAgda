
{-# OPTIONS --without-K --no-import-sorts #-}
module UniAgda.Equiv.ClosureProperties where

open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Functions
open import UniAgda.Core.Types.Identity
open import UniAgda.Core.Types.Sigma
open import UniAgda.Core.Types.Unit

open import UniAgda.Core.Homotopy
open import UniAgda.Core.Equivalences

-- * 2-out-of-3
-- Equivalences satisfy the 2-out-of-3 property, which states that
-- given a commuting triangle of equivalences, if any two of them are
-- equivalences, then the third one is. We know that composing two
-- equivalences is an equivalence, so we need to show that the other
-- two parts hold.
--  Theorem4.7.1

equiv2-out-of-3i : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} {f : A → B} {g : B → C}
                  → isEquiv f → isEquiv (g o f)
                  → isEquiv g
equiv2-out-of-3i {f = f} {g = g} (f' , α , β , γ) (gf' , α' , β' , γ') =
  isequiv-adjointify
    (f o gf' ,
    β' ,
    λ y →
      ap (f o gf' o g) (β y ^) ∘
      ap f (α' (f' y)) ∘
      (β y))


equiv2-out-of-3ii : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} {f : A → B} {g : B → C}
                  → isEquiv g → isEquiv (g o f)
                  → isEquiv f
equiv2-out-of-3ii {f = f} {g = g} (g' , α , β , γ) (gf' , α' , β' , γ') =
  isequiv-adjointify
    ((λ z → gf' (g z)) ,
    (λ y →
      (α ((f o gf' o g) y) ^) ∘
      ap g' (β' (g y)) ∘
      (α y)) ,
    α')

-- * Retracts
-- We first define retracts, as a record to keep it a tidy definition.
--  Definition4.7.2

record retract {i j k l : Level} {A : Type i} {B : Type j} {X : Type k} {Y : Type l} (g : A → B) (f : X → Y) : Type (i ⊔ j ⊔ k ⊔ l) where
       eta-equality
       field
         top-left : A → X
         top-right : X → A
         bot-left : B → Y
         bot-right : Y → B

         top-id : top-right o top-left ~ id
         bot-id : bot-right o bot-left ~ id
         left-square : f o top-left ~ bot-left o g
         right-square : g o top-right ~ bot-right o f

         rectangle : (a : A) → ap g (top-id a) ∘ bot-id (g a) ^ ≡ right-square (top-left a) ∘ ap bot-right (left-square a)

retract-of-types : ∀ {i j} (A : Type i) (B : Type j)
                   → Type (i ⊔ j)
retract-of-types A B = retract (λ (a : A) → tt) (λ (b : B) → tt)


--  Lemma4.7.3


-- private
--   lemma4-7-3-help1 : ∀ {i j k l} {A : Type i} {B : Type j} {X : Type k} {Y : Type l}
--                      (g : A → B) (f : X → Y) (H : retract g f) (b : B)
--                      → fib g b → fib f (retract.bot-left H b)
--   lemma4-7-3-help1 g f H b (a , p) = retract.top-left H a , retract.left-square H a ∘ (ap (retract.bot-left H) p)

--   lemma4-7-3-help2 : ∀ {i j k l} {A : Type i} {B : Type j} {X : Type k} {Y : Type l}
--                      (g : A → B) (f : X → Y) (H : retract g f) (b : B)
--                      → fib f (retract.bot-left H b) → fib g b
--   lemma4-7-3-help2 g f H b (x , q) = (retract.top-right H x) , (retract.right-square H x ∘ ap (retract.bot-right H) q ∘ retract.bot-id H b)

--   lemma4-7-3-help3 : ∀ {i j k l} {A : Type i} {B : Type j} {X : Type k} {Y : Type l}
--                      (g : A → B) (f : X → Y) (H : retract g f)
--                      → (a : A) → (lemma4-7-3-help2 g f H (g a) (lemma4-7-3-help1 g f H (g a) ((a , refl))) ≡ (a , refl))
--                      → ((b : B) (a : A) (p : g a ≡ b) → lemma4-7-3-help2 g f H b (lemma4-7-3-help1 g f H b (a , p)) ≡ (a , p))
--   lemma4-7-3-help3 g f H a x b a' p = {!!}


-- retract-fibres : ∀ {i j k l} {A : Type i} {B : Type j} {X : Type k} {Y : Type l}
--                  (g : A → B) (f : X → Y) (H : retract g f)
--                  → ((b : B) → retract-of-types (fib g b) (fib f (retract.bot-left H b)))
-- retract.top-left (retract-fibres g f H b) (a , p) = lemma4-7-3-help1 g f H b (a , p)
-- retract.top-right (retract-fibres g f H b) (x , q) = lemma4-7-3-help2 g f H b (x , q)
-- retract.bot-left (retract-fibres g f H b) = id
-- retract.bot-right (retract-fibres g f H b) = id
-- retract.top-id (retract-fibres g f H b) (a , p) = lemma4-7-3-help3 g f H a (path-equiv-sigma ({!!} , {!!}) ) b a p
-- retract.bot-id (retract-fibres g f H b) = hrefl
-- retract.left-square (retract-fibres g f H b) x = refl
-- retract.right-square (retract-fibres g f H b) (a , b₁) = Unit-is-prop _ _
-- retract.rectangle (retract-fibres g f H b) a = Unit-is-set _ _ _ _
