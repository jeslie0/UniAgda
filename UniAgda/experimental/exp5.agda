{-# OPTIONS --without-K --rewriting  #-}
module UniAgda.experimental.exp5 where

open import UniAgda.Core.Everything
open import UniAgda.HITs.PropTrunc
open import UniAgda.Categories.Everything



lemma : ∀ {i} → isSet (Prop_ i)
lemma (A , X) (B , Y) =
  equiv-base-Pi
    thm2-7-2
    λ { (p , b) → equiv-base-Pi thm2-7-2
      λ { (q , c) → ap path-equiv-sigma (path-equiv-sigma ({!!} , {!!}))}}


open Precategory

Fin-set' : (i : Level) → Precategory lzero lzero
ob (Fin-set' i) = ℕ
hom (Fin-set' i) n m = Fin n → Fin m
hom-set (Fin-set' i) n m = func-of-sets-is-set (Fin-n-is-set m)
Id (Fin-set' i) = id
comp (Fin-set' i) g f = g o f
IdL (Fin-set' i) f = funext λ x → refl
IdR (Fin-set' i) f = funext λ x → refl
Assoc (Fin-set' i) f g h = funext λ x → refl


test : ∀ (i) → Functor (Fin-set' i) (FIN-SET i)
Functor.F₀ (test i) n = (raise i $ Fin n) , n , ∣ equiv-adjointify ((λ x →  map-inv-raise x) , ((λ x → map-raise  x) , ((λ {x → refl}) , λ { (map-raise x) → refl}))) ∣
Functor.F₁ (test i) f (map-raise a) = map-raise (f a)
Functor.F-id (test i) {a} = funext λ { (map-raise x) → refl}
Functor.F-comp (test i) g f = funext λ { (map-raise x) → refl}


foo : ∀ (i) → isCatEquiv (test i)
isLeftAdjoint.Right (isCatEquiv.adj (foo i)) = {!!}
isLeftAdjoint.unit (isCatEquiv.adj (foo i)) = {!!}
isLeftAdjoint.counit (isCatEquiv.adj (foo i)) = {!!}
isLeftAdjoint.left-triangle (isCatEquiv.adj (foo i)) = {!!}
isLeftAdjoint.right-triangle (isCatEquiv.adj (foo i)) = {!!}
isCatEquiv.unit-is-iso (foo i) = {!!}
isCatEquiv.counit-is-iso (foo i) = {!!}







ℜel : (i j : Level) → Precategory (lsuc i) (lsuc i)
Precategory.ob (ℜel i j) = Set_ i
Precategory.hom (ℜel i j) (A , X) (B , Y) = A → B → Prop_ i
hom-set (ℜel i j) (A , X) (B , y) = func-of-sets-is-set (func-of-sets-is-set {!!})
Id (ℜel i j) {A , X} a b = (a ≡ b) , (X a b)
comp (ℜel i j) {A , X} {B , Y} {C , Z} S R a c = ∥ Σ[ b ∈ B ] (pr₁ (R a b) × pr₁ (S b c) ) ∥ , prop-trunc-is-prop _
IdL (ℜel i j) {A , X} {B , Y} f =
  funext λ a →
  funext λ b →
    fibres-props-eq
      isProp-is-prop
      _
      _
      (ua (
        equiv-adjointify
          ((prop-trunc-rec (pr₂ (f a b)) (λ { (x , p , z) → transport (λ Z → pr₁ (f Z b)) (p ^) z})) ,
          (λ x → ∣ a , (refl , x) ∣) ,
          (λ x →  pr₂ (f a b) _ _) ,
          prop-trunc-ind
            (λ x → props-are-sets (prop-trunc-is-prop _) _ _)
            λ { (x , p , z) → prop-trunc-is-prop _ _ _})))
Precategory.IdR (ℜel i j) = {!!}
Precategory.Assoc (ℜel i j) = {!!}











