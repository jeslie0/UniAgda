{-# OPTIONS --without-K #-}
module UniAgda.categories.precategory where

open import UniAgda.core.CORE public

record Precategory {i j} : Type (lsuc (i ⊔ j)) where
  no-eta-equality
  field
    ob : Type i
    hom : (a b : ob) → Type j
    hom-set : (a b : ob) → isSet (hom a b)
    Id : {a : ob} → (hom a a)
    comp : {a b c : ob} → (hom b c) → hom a b → hom a c
    l-Id : {a b : ob} (f : hom a b) → comp f Id ≡ f
    r-Id : {a b : ob} (f : hom a b) → comp Id f ≡ f
    ass : {a b c d : ob} (f : hom a b) (g : hom b c) (h : hom c d) → comp h (comp g f) ≡ comp (comp h g) f

open Precategory public


is-iso : ∀ {i j} {∁ : Precategory {i} {j}} {a b : ob ∁}
      (f : hom ∁ a b)
      → Type j
is-iso {i} {j} {∁} {a} {b} f = Σ[ g ∈ (hom ∁ b a) ] ((comp ∁ f g ≡ Precategory.Id ∁) × (comp ∁ g f ≡ Precategory.Id ∁))


iso : ∀ {i j} {∁ : Precategory {i} {j}}
      (a b : ob ∁)
      → Type j
iso {i} {j} {∁} a b = Σ[ f ∈ (hom ∁ a b) ] (is-iso {i} {j} {∁} {a} {b} f)


{- iso is equivalence relation -}

iso-refl : ∀ {i j} {∁ : Precategory {i} {j}}
           (a : ob ∁)
           -> iso {_} {_} {∁} a a
iso-refl {i} {j} {∁} a = (Id ∁) , ((Id ∁) , ((l-Id ∁ (Id ∁)) , (r-Id ∁ (Id ∁))))

iso-sym : ∀ {i j} {∁ : Precategory {i} {j}}
          {a b : ob ∁}
          -> (iso {_} {_} {∁} a b) -> (iso {_} {_} {∁} b a)
iso-sym {i} {j} {∁} {a} {b} (f , g , x , y) = g , (f , (y , x))

iso-trans : ∀ {i j} {∁ : Precategory {i} {j}}
            {a b c : ob ∁}
            -> (iso {_} {_} {∁} a b) -> (iso {_} {_} {∁} b c) -> (iso {_} {_} {∁} a c) 
iso-trans {i} {j} {∁} {a} {b} {c} (f , g , x , y) (f' , g' , x' , y') = (comp ∁ f' f) ,
                                                                        ((comp ∁ g g') ,
                                                                        (((ass ∁ g' g _) ∘ transport (λ Z → comp ∁ Z g' ≡ Id ∁) (ass ∁ _ _ _) (transport (λ Z → comp ∁ (comp ∁ f' Z ) g' ≡ Id ∁) (x ^) (transport (λ Z → comp ∁ Z g' ≡ Id ∁) (l-Id ∁ f' ^) x')) ) ,
                                                                        ((ass ∁ _ g' g) ^ ∘ transport (λ Z → comp ∁ g Z ≡ Id ∁) (ass ∁ _ _ _ ^) (transport (λ Z → comp ∁ g (comp ∁ Z f) ≡ Id ∁) (y' ^) (transport (λ Z → comp ∁ g Z ≡ Id ∁) (r-Id ∁ f ^) y)) )))


iso-of-f-is-prop : ∀ {i j} {∁ : Precategory {i} {j}} {a b : ob ∁} (f : hom ∁ a b)
             → isProp (is-iso {i} {j} {∁} {a} {b} f)
iso-of-f-is-prop {i} {j} {∁} {a} {b} f (g , η , ε) (g' , η' , ε') =  path-equiv-sigma _ _
           (r-Id ∁ g ^ ∘ transport (λ X → comp ∁ X g ≡ g') (ε') ((ass ∁ _ _ _) ^ ∘ transport (λ X → comp ∁ g' X ≡ g') (η ^) (l-Id ∁ g') ) , path-equiv-prod ((hom-set ∁ _ _ _ _ _ η') , hom-set ∁ _ _ _ _ _ ε')) 

iso-is-set : ∀ {i j} {∁ : Precategory {i} {j}}
             (a b : ob ∁)
             → isSet (iso {_} {_} {∁} a b)
iso-is-set {_} {_} {∁} a b = prop-fibres-totalspace-set (hom-set ∁ a b) λ x → iso-of-f-is-prop {_} {_} {∁} x
