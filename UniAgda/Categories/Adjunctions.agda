{-# OPTIONS --without-K --no-import-sorts #-}
module UniAgda.Categories.Adjunctions where

open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Functions
open import UniAgda.Core.Types.Identity
open import UniAgda.Core.Types.Sigma

open import UniAgda.Categories.Category
open import UniAgda.Categories.Functor
open import UniAgda.Categories.Natural-Transformation

open import UniAgda.Core.PathSpaces.Sigma

open import UniAgda.Core.Axioms

open import UniAgda.Core.Equivalences


open import UniAgda.Categories.Category
open import UniAgda.Categories.Functor
open import UniAgda.Categories.Natural-Transformation

-- * Definition

record isLeftAdjoint {i j k l : Level} {A : Precategory i j} {B : Precategory k l} (Left : Functor A B) : Type (i ⊔ j ⊔ k ⊔ l) where
  eta-equality
  field
    Right : Functor B A
    unit : NaturalTransformation Idᶠ (Right oF Left)
    counit : NaturalTransformation (Left oF Right) Idᶠ

  module unit = NaturalTransformation unit
  module counit = NaturalTransformation counit
  module Left = Functor Left
  module Right = Functor Right
  module A = Precategory A
  module B = Precategory B

  field
    left-triangle : (a : A.ob) → B.comp (counit.α-ob (Left.₀ a)) (Left.₁ (unit.α-ob a)) ≡ B.Id {Left.₀ a}
    right-triangle : (b : B.ob) → A.comp (Right.₁ (counit.α-ob b)) (unit.α-ob (Right.₀ b)) ≡ A.Id {Right.₀ b}

-- ** Sigma version

isLeftAdjoint-sig : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l}
                    (Left : Functor A B)
                    → Type (i ⊔ j ⊔ k ⊔ l)
isLeftAdjoint-sig {A = A} {B = B} Left =
  let module A = Precategory A in
  let module B = Precategory B in
  let module Left = Functor Left in
  Σ[ Right ∈ (Functor B A) ] (
    Σ[ unit ∈ (NaturalTransformation Idᶠ (Right oF Left)) ] (
      Σ[ counit ∈ (NaturalTransformation (Left oF Right) Idᶠ) ](
        let module Right = Functor Right in
        let module unit = NaturalTransformation unit in
        let module counit = NaturalTransformation counit in
        Σ[ left-triangle ∈ ( (a : A.ob) → B.comp (counit.α-ob (Left.₀ a)) (Left.₁ (unit.α-ob a)) ≡ B.Id {Left.₀ a}) ](
           (b : B.ob) → A.comp (Right.₁ (counit.α-ob b)) (unit.α-ob (Right.₀ b)) ≡ A.Id {Right.₀ b}))))

isLeftAdjoint-sig→rec : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l} {Left : Functor A B}
                         (adj : isLeftAdjoint-sig Left)
                         → isLeftAdjoint Left
isLeftAdjoint.Right (isLeftAdjoint-sig→rec adj) = pr₁ adj
isLeftAdjoint.unit (isLeftAdjoint-sig→rec adj) = pr₁ (pr₂ adj)
isLeftAdjoint.counit (isLeftAdjoint-sig→rec adj) = pr₁ (pr₂ (pr₂ adj))
isLeftAdjoint.left-triangle (isLeftAdjoint-sig→rec adj) = pr₁ (pr₂ (pr₂ (pr₂ adj)))
isLeftAdjoint.right-triangle (isLeftAdjoint-sig→rec adj) =  pr₂ (pr₂ (pr₂ (pr₂ adj)))

isLeftAdjoint-rec→sig : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l} {Left : Functor A B}
                        (adj : isLeftAdjoint Left)
                        → isLeftAdjoint-sig Left
isLeftAdjoint-rec→sig adj =
  let module adj = isLeftAdjoint adj in
  adj.Right ,
  adj.unit ,
  adj.counit ,
  adj.left-triangle ,
  adj.right-triangle

isLeftAdjoint-rec→sig→rec : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l} {Left : Functor A B}
                            (adj : isLeftAdjoint Left)
                            → (isLeftAdjoint-sig→rec o isLeftAdjoint-rec→sig) adj ≡ adj
isLeftAdjoint-rec→sig→rec adj = refl

isLeftAdjoint-sig→rec→sig : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l} {Left : Functor A B}
                            (adj : isLeftAdjoint-sig Left)
                            → (isLeftAdjoint-rec→sig {Left = Left} o isLeftAdjoint-sig→rec) adj ≡ adj
isLeftAdjoint-sig→rec→sig (Right , unit , counit , left-triangle , right-triangle) =
  path-equiv-sigma (refl ,
    path-equiv-sigma (refl ,
      (path-equiv-sigma (refl ,
        (path-equiv-sigma (refl ,
          refl))))))

isLeftAdjoint-sig-Equiv : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l} {Left : Functor A B}
                          → isLeftAdjoint-sig Left ≃ isLeftAdjoint Left
isLeftAdjoint-sig-Equiv {Left = Left} = equiv-adjointify
  (isLeftAdjoint-sig→rec ,
  isLeftAdjoint-rec→sig ,
  isLeftAdjoint-rec→sig→rec ,
  isLeftAdjoint-sig→rec→sig {Left = Left})

-- * Properties
-- If A is a category, then the type "F is a left adjoint" is a mere proposition.

-- isLeftAdjoint-is-prop : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l} {H : isCategory A}
--                         (F : Functor A B)
--                         → isProp (isLeftAdjoint F)
-- isLeftAdjoint-is-prop {A = A} {B = B} {H = H} F =
--   equiv-with-prop (isLeftAdjoint-sig-Equiv)
--     λ { (G , η , ϵ) (G' , η' , ϵ') → {!!}}
