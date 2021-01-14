{-# OPTIONS --without-K #-}
module UniAgda.e-cat.functor where

open import UniAgda.e-cat.precategory public


record Functor {i j k l} (A : Precategory i j) (B : Precategory k l) : Type (i ⊔ j ⊔ k ⊔ l) where
  no-eta-equality
  open Precategory
  field
    F-ob : A .ob → B .ob
    F-hom : {a b : Precategory.ob A} → Precategory.hom A a b → Precategory.hom B (F-ob a) (F-ob b)
    F-id : {a : Precategory.ob A} → F-hom (Precategory.Id A {a}) ≡ (Precategory.Id B {F-ob a})
    F-nat : {a b c : Precategory.ob A} (g : Precategory.hom A b c) (f : Precategory.hom A a b) → F-hom (Precategory.comp A g f) ≡ Precategory.comp B (F-hom g) (F-hom f)


Functor-Sig : ∀ {i j k l}
          (A : Precategory i j) (B : Precategory k l)
          → Type (i ⊔ j ⊔ k ⊔ l)
Functor-Sig {i} {j} {k} {l} A B =
  let module A = Precategory A in
    let module B = Precategory B in
      Σ[ F-ob ∈ ((A.ob) → (B.ob))] (
        Σ[ F-hom ∈ ({a b : A.ob} → A.hom a b → B.hom (F-ob a) (F-ob b))] (
          Σ[ F-id ∈ ({a : A.ob} → F-hom (A.Id {a}) ≡ (B.Id {F-ob a}))] (
            ({a b c : A.ob} (g : A.hom b c) (f : A.hom a b) → F-hom (A.comp g f) ≡ B.comp (F-hom g) (F-hom f)))))

postulate
  Functor-Sig-eq : ∀ {i j k l} → Functor-Sig {i} {j} {k} {l} ≡ Functor {i} {j} {k} {l}

-- open functor public
{- Functor composition -}

{- Identity functor -}
Idᶠ : ∀ {i j} {C : Precategory i j}
      → Functor C C
Functor.F-ob (Idᶠ {i} {j} {C}) = id
Functor.F-hom (Idᶠ {i} {j} {C}) = id
Functor.F-id (Idᶠ {i} {j} {C}) = refl
Functor.F-nat (Idᶠ {i} {j} {C}) g f = refl



