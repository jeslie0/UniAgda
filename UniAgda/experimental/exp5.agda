{-# OPTIONS --without-K --rewriting  #-}
module UniAgda.experimental.exp5 where

open import UniAgda.Core.Everything
open import UniAgda.HITs.PropTrunc
open import UniAgda.Categories.Everything





open Precategory

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



CAT : (i j : Level) → Precategory (lsuc i ⊔ lsuc j) (i ⊔ j)
ob (CAT i j) = Precategory i j
hom (CAT i j) A B = Functor A B
hom-set (CAT i j) A B =
  equiv-with-set
    (Functor-sig-Equiv A B)
    λ {(F₀ , F₁ , Fa) (G₀ , G₁ , Ga) → equiv-base-Pi thm2-7-2
      λ { (p , q) → equiv-base-Pi thm2-7-2
        λ { (r , s) → ap path-equiv-sigma (path-equiv-sigma ({!!} , {!!}))}}}
Id (CAT i j) = Idᶠ
comp (CAT i j) = compᶠ
IdL (CAT i j) F = F-o-Id ^
IdR (CAT i j) F = Id-o-F ^
Assoc (CAT i j) F G H = F-Assoc F G H ^









