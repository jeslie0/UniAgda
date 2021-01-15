{-# OPTIONS --without-K  #-}
module UniAgda.categories.categories.functorcat where

open import UniAgda.categories.category public
open import UniAgda.categories.functor public
open import UniAgda.categories.natural-transformation public

_^_ : ∀ {i j k l} (A : Precategory {i} {j}) (B : Precategory {k} {l}) → Precategory {k ⊔ l ⊔ i ⊔ j} {k ⊔ l ⊔ j}
_^_ {i} {j} {k} {l} A B =
  functor {_} {_} {_} {_} B A ,
  (λ F G → nat-trans {k} {l} {i} {j} {B} {A} F G) ,
  nat-trans-form-set {_} {_} {_} {_} {B} {A}  ,
  (λ { {F} → idⁿ {_} {_} {_} {_} {B} {A} {F}}) ,
  (λ { {F} {G} {H} → nat-trans-compᵛ {_} {_} {_} {_} {B} {A} {F} {G} {H}}) ,
  (λ { {F} {G} α → nat-trans-compᵛ-id _ _ α}) ,
  (λ { {F} {G} α → nat-trans-id-compᵛ _ _ α}) ,
  nat-trans-comp-assoc



private
  lemma9-2-4i : ∀ {i j k l} {A : Precategory {i} {j}} {B : Precategory {k} {l}} {F G : ob (B ^ A)} {γ : hom (B ^ A) F G}
              → (isIso {_} {_} {B ^ A} {F} {G} γ) → ((a : ob A) → isIso {_} {_} {B} (α-ob {_} {_} {_} {_} {A} {B} {F} {G} γ a))
  lemma9-2-4i {i} {j} {k} {l} {A} {B} {F} {G} {γ₁ , γ₂} ((δ₁ , δ₂) , p , q) a =
    (α-ob {_} {_} {_} {_} {A} {B} {G} {F} (δ₁ , δ₂) a ) ,
    happlyD (pr₁ (path-sigma p)) a ,
    happlyD (pr₁ (path-sigma q)) a

  lemma9-2-4ii : ∀ {i j k l} {A : Precategory {i} {j}} {B : Precategory {k} {l}} {F G : ob (B ^ A)} {γ : hom (B ^ A) F G}
              → ((a : ob A) → isIso {_} {_} {B} (α-ob {_} {_} {_} {_} {A} {B} {F} {G} γ a)) → (isIso {_} {_} {B ^ A} {F} {G} γ)
  lemma9-2-4ii {i} {j} {k} {l} {A} {B} {F} {G} {γ₁ , γ₂} X =
    ((λ a → pr₁ (X a)) ,
      λ a b f → l-Id B ((pr₁ (X b)) $o (F-hom G f)) ^ ∘ {!!}) ,
    {!!} ,
    {!!}



lemma9-2-4 : ∀ {i j k l} {A : Precategory {i} {j}} {B : Precategory {k} {l}} {F G : ob (B ^ A)} {γ : hom (B ^ A) F G}
             → (isIso {_} {_} {B ^ A} {F} {G} γ) ↔ ((a : ob A) → isIso {_} {_} {B} (α-ob {_} {_} {_} {_} {A} {B} {F} {G} γ a))
lemma9-2-4 {i} {j} {k} {l} {A} {B} {F} {G} {γ} =
  lemma9-2-4i ,
  lemma9-2-4ii





thm9-2-5 : ∀ {i j k l} {A : Precategory {i} {j}} {B : Precategory {k} {l}}
           → isCategory B
           → isCategory (B ^ A)
thm9-2-5 {i} {j} {k} {l} {A} {B} X F G = {!!}
