{-# OPTIONS --without-K #-}
module UniAgda.core.prop-set-properties where

open import UniAgda.core.axioms public
open import UniAgda.core.path-spaces public

unit-is-set : isSet Unit
unit-is-set x y = transport (λ X → (p q : X) → p ≡ q) (ua (thm2-8-1 x y) ^) λ { tt tt → refl}
ex3-1-2 = unit-is-set

empty-is-set : isSet Empty
empty-is-set () y
ex3-1-3 = empty-is-set


x-in-prop-equiv-unit : {i : Level} {P : Type i}
                       → isProp P → P
                       → P ≃ Unit
x-in-prop-equiv-unit X x₀ = equiv-adjointify ((λ x → tt) , ((λ x → x₀) , ((λ { tt → refl}) , λ x → X x₀ x)))
lemma3-3-2 = x-in-prop-equiv-unit

props-equiv : {i j : Level} {P : Type i} {Q : Type j}
         → isProp P → isProp Q → (P → Q) → (Q → P)
         → P ≃ Q
props-equiv {i} {j} {P} {Q} X Y f g = equiv-adjointify (f , g , ((λ y → Y ((f o g) y) y) , λ x → X ((g o f) x) x))
lemma3-3-3 = props-equiv

lemma3-3-4-help : {i : Level} {A : Type i} {f : (x y : A) → x ≡ y} {x : A}
                  → (y z : A) (p : y ≡ z)
                  → (f x y) ∘ p ≡ f x z
lemma3-3-4-help {_} {A} {f} {x} y z p = lemma2-11-2i x p (f x y) ^ ∘ apD (λ y → f x y) p

props-are-sets : {i : Level} {A : Type i}
             → isProp A → isSet A
props-are-sets {i} {A} f x y p q = pq=s-to-q=p^s (f x x) p (f x y) (lemma3-3-4-help {_} {_} {f} {x} x y p) ∘ pq=s-to-q=p^s {_} {A} {_} {_} {_} (f x x) q (f x y) (lemma3-3-4-help {_} {_} {f} {x} x y q) ^


lemma3-3-4 = props-are-sets

isProp-is-prop : {i : Level}
                  (A : Type i)
                  → isProp (isProp A)
isProp-is-prop A f g = funextD λ x → funextD λ y → props-are-sets f x y (f x y) (g x y)
lemma3-3-5i = isProp-is-prop
