{-# OPTIONS --without-K  --no-import-sorts #-}
module UniAgda.Categories.Functor where

open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Functions
open import UniAgda.Core.Types.Identity
open import UniAgda.Core.Types.Sigma

open import UniAgda.Core.Equivalences

open import UniAgda.Core.PathSpaces.Sigma

open import UniAgda.Core.Axioms

open import UniAgda.Categories.Category

open Precategory

-- * Definition
-- We introduce functors between precategories as a record, giving the
-- sigma type and equivalence later.

record Functor {i j k l} (A : Precategory i j) (B : Precategory k l) : Type (i ⊔ j ⊔ k ⊔ l) where
  eta-equality
  private module A = Precategory A
  private module B = Precategory B
  field
    F₀ : A .ob → B .ob
    F₁ : {a b : A .ob} → A [ a , b ] →  B [ (F₀ a) , (F₀ b) ]
    F-id : {a : A .ob} → F₁ (A .Id {a}) ≡ (B .Id {F₀ a})
    F-comp : {a b c : A .ob} (g : A [ b , c ]) (f : A [ a , b ]) → F₁ (g o⟨ A ⟩ f) ≡ (F₁ g) o⟨ B ⟩ (F₁ f)

  ₀ = F₀
  ₁ = F₁

-- ** Sigma definition and equivalence

Functor-sig : ∀ {i j k l}
          (A : Precategory i j) (B : Precategory k l)
          → Type (i ⊔ j ⊔ k ⊔ l)
Functor-sig {i} {j} {k} {l} A B =
  let module A = Precategory A in
    let module B = Precategory B in
      Σ[ F₀ ∈ ((A.ob) → (B.ob))] (
        Σ[ F₁ ∈ ({a b : A.ob} → A.hom a b → B.hom (F₀ a) (F₀ b))] (
          Σ[ F-id ∈ ({a : A.ob} → F₁ (A.Id {a}) ≡ (B.Id {F₀ a}))] (
            ({a b c : A.ob} (g : A.hom b c) (f : A.hom a b) → F₁ (A.comp g f) ≡ B.comp (F₁ g) (F₁ f)))))

functor-sig→rec : ∀ {i j k l}
                  {A : Precategory i j} {B : Precategory k l}
                  → Functor-sig A B → Functor A B
functor-sig→rec (F₀ , F₁ , F-id , F-comp) =
  record { F₀ = F₀ ; F₁ = F₁ ; F-id = F-id ; F-comp = F-comp }

functor-rec→sig : ∀ {i j k l}
                  {A : Precategory i j} {B : Precategory k l}
                  → Functor A B → Functor-sig A B
functor-rec→sig record { F₀ = F₀ ; F₁ = F₁ ; F-id = F-id ; F-comp = F-comp } =
  (F₀ ,
  F₁ ,
  F-id ,
  F-comp)

functor-rec→sig→rec : ∀ {i j k l}
                      {A : Precategory i j} {B : Precategory k l}
                      → (F : Functor A B) → (functor-sig→rec o functor-rec→sig) F ≡ F
functor-rec→sig→rec F = refl

functor-sig→rec→sig : ∀ {i j k l}
                      {A : Precategory i j} {B : Precategory k l}
                      → (F : Functor-sig A B) → (functor-rec→sig o functor-sig→rec {A = A} {B = B}) F ≡ F
functor-sig→rec→sig (F₀ , F₁ , F-id , F-comp) =
  path-equiv-sigma (refl ,
    (path-equiv-sigma (refl ,
      (path-equiv-sigma (refl ,
        refl)))))

Functor-sig-Equiv : ∀ {i j k l}
                    {A : Precategory i j} {B : Precategory k l}
                    → Functor-sig A B ≃ Functor A B
Functor-sig-Equiv = equiv-adjointify
  (functor-sig→rec ,
  functor-rec→sig ,
  functor-rec→sig→rec ,
  functor-sig→rec→sig)



open Functor

-- * Paths between functors
-- To show two functors are equal, it suffices to show only that they
-- are equal on objects and maps. This is because the last two
-- components in the definition are mere propositions, following from
-- precategories having hom sets.

Functor-path : ∀ {i₁ i₂ i₃ i₄} {A : Precategory i₁ i₂} {B : Precategory i₃ i₄}
               {F G : Functor A B} (p : F .F₀ ≡ G .F₀) (q : transport (λ F₀ →  Σ[ F₁ ∈ ({a b : A .ob} → A .hom a b → B .hom (F₀ a) (F₀ b))] (
          Σ[ F-id ∈ ({a : A .ob} → F₁ (A .Id {a}) ≡ (B .Id {F₀ a}))] (
            ({a b c : A .ob} (g : A .hom b c) (f : A .hom a b) → F₁ (A .comp g f) ≡ B .comp (F₁ g) (F₁ f))))) p (pr₂ (functor-rec→sig F)) ≡ pr₂ (functor-rec→sig G))
               → F ≡ G
Functor-path {A = A} {B = B} p q =
  equiv-types-eq (Functor-sig-Equiv)
  (path-equiv-sigma (p ,
    (path-equiv-sigma (ap pr₁ q ,
      path-equiv-sigma (implicit-funext (λ x → B .hom-set _ _ _ _ _ _) ,
        implicit-funext λ x →
        implicit-funext λ y →
        implicit-funext λ z →
        funextD λ f →
        funextD λ g → B .hom-set _ _ _ _ _ _)))))

-- * Functor composition

-- compᶠ : ∀ {i₁ i₂ i₃ i₄ i₅ i₆} {A : Precategory i₁ i₂} {B : Precategory i₃ i₄} {C : Precategory i₅ i₆}
--           (G : Functor B C) (F : Functor A B)
--           → Functor A C
-- F₀ (compᶠ G F) = G .F₀ o F .F₀
-- F₁ (compᶠ G F) = G .F₁ o F .F₁
-- F-id (compᶠ {C = C} G F) = transport (λ Z → G .F₁ (Z) ≡ C .Id) (F .F-id ^) (G .F-id)
-- F-comp (compᶠ G F) g f = ap (G .F₁) (F. F-comp g f) ∘ G . F-comp (F .F₁ g) (F .F₁ f)

-- _oF_ = compᶠ
-- infixr 9 _oF_


-- This composition is associative.

-- F-Assoc : ∀ {i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈} {A : Precategory i₁ i₂} {B : Precategory i₃ i₄} {C : Precategory i₅ i₆} {D : Precategory i₇ i₈}
--             (F : Functor A B) (G : Functor B C) (H : Functor C D)
--             → (H oF G) oF F ≡ H oF (G oF F)
-- F-Assoc {D = D} F G H =
--   Functor-path
--     refl
--     (path-equiv-sigma (refl ,
--       (path-equiv-sigma (implicit-funext (λ x → D .hom-set _ _ _ _ _ _) ,
--         implicit-funext λ x →
--         implicit-funext λ y →
--         implicit-funext λ x₁ →
--         funextD λ x₂ →
--         funextD λ x₃ →
          -- D .hom-set _ _ _ _ _ _))))


-- * Identity functor

-- Idᶠ : ∀ {i j} {C : Precategory i j}
--       → Functor C C
-- F₀ (Idᶠ {i} {j} {C}) = id
-- F₁ (Idᶠ {i} {j} {C}) = id
-- F-id (Idᶠ {i} {j} {C}) = refl
-- F-comp (Idᶠ {i} {j} {C}) g f = refl

-- F-o-Id : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l} {F : Functor A B}
--          → F ≡ compᶠ F Idᶠ
-- F-o-Id =
--   Functor-path
--     refl
--     refl

-- Id-o-F : ∀ {i j k l} {A : Precategory i j} {B : Precategory k l} {F : Functor A B}
--          → F ≡ compᶠ Idᶠ F
-- Id-o-F {B = B} =
--   Functor-path
--     refl
--     (path-equiv-sigma (refl ,
--       (path-equiv-sigma ((implicit-funext (λ x → B .hom-set _ _ _ _ _ _)) ,
--         implicit-funext λ x →
--         implicit-funext λ x₁ →
--         implicit-funext λ x₂ →
--         funextD λ x₃ →
--         funextD λ x₄ →
--           B .hom-set _ _ _ _ _ _))))
