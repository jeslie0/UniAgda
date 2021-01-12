{-# OPTIONS --without-K #-}
module UniAgda.categories.precat where

open import UniAgda.core.CORE public

Precategory : ∀ {i j} → Type (_)
Precategory {i} {j} =
  Σ[ ob ∈ (Type i) ] (
    Σ[ hom ∈ ((a b : ob) → Type j) ] (
      Σ[ hom-set ∈ ((a b : ob) → isSet (hom a b)) ] (
        Σ[ Id ∈ ({a : ob} → (hom a a)) ] (
          Σ[ comp ∈ ({a b c : ob} → (hom b c) → hom a b → hom a c) ] (
            Σ[ l-Id ∈ ({a b : ob} (f : hom a b) → comp f Id ≡ f) ] (
              Σ[ r-Id ∈ ({a b : ob} (f : hom a b) → comp Id f ≡ f) ] (
                {a b c d : ob} (f : hom a b) (g : hom b c) (h : hom c d) → comp h (comp g f) ≡ comp (comp h g) f)))))))

ob : ∀ {i j} (C : Precategory {i} {j})
     → Type i
ob (a , a₁ , a₂ , a₃ , a₄ , a₅ , a₆ , b) = a

hom : ∀ {i j} (C : Precategory {i} {j})
      → (a b : ob C) → Type j
hom (a , a₁ , a₂ , a₃ , a₄ , a₅ , a₆ , b) = a₁

hom-set : ∀ {i j} (C : Precategory {i} {j})
          → (a b : ob C) → isSet (hom C a b)
hom-set (a , a₁ , a₂ , a₃ , a₄ , a₅ , a₆ , b) = a₂

Id : ∀ {i j} (C : Precategory {i} {j})
     → {a : ob C} → (hom C a a)
Id (a , a₁ , a₂ , a₃ , a₄ , a₅ , a₆ , b) = a₃

comp : ∀ {i j} (C : Precategory {i} {j})
       → {a b c : ob C} → (hom C b c) → hom C a b → hom C a c
comp (a , a₁ , a₂ , a₃ , a₄ , a₅ , a₆ , b) = a₄

l-Id : ∀ {i j} (C : Precategory {i} {j})
       → {a b : ob C} (f : hom C a b) → comp C f (Id C) ≡ f
l-Id (a , a₁ , a₂ , a₃ , a₄ , a₅ , a₆ , b) = a₅

r-Id : ∀ {i j} (C : Precategory {i} {j})
       → {a b : ob C} (f : hom C a b) → comp C (Id C) f ≡ f
r-Id (a , a₁ , a₂ , a₃ , a₄ , a₅ , a₆ , b) = a₆

ass : ∀ {i j} (C : Precategory {i} {j})
      → {a b c d : ob C} (f : hom C a b) (g : hom C b c) (h : hom C c d) → comp C h (comp C g f) ≡ comp C (comp C h g) f
ass (a , a₁ , a₂ , a₃ , a₄ , a₅ , a₆ , b) = b



-- _$_o_ : ∀ {i j} {C : Precategory {i} {j}} {a b c : ob C}
--        (g : hom C b c) (f : hom C a b)
--        → hom C a c
-- _$o_ {i} {j} {C} {a} {b} {c} g f = comp C g f

{- The opposite category -}
_^op : ∀ {i j} (∁ : Precategory {i} {j}) → Precategory {i} {j}
C ^op =
  ob C ,
  (λ a b → hom C b a) ,
  (λ a b → hom-set C b a) ,
  Id C ,
  (λ f g → comp C g f) ,
  (λ f → r-Id C f) ,
  (λ f → l-Id C f) ,
  λ f g h → ass C h g f ^



isIso : ∀ {i j} {∁ : Precategory {i} {j}} {a b : ob ∁}
      (f : hom ∁ a b)
      → Type j
isIso {i} {j} {∁} {a} {b} f = Σ[ g ∈ (hom ∁ b a) ] ((comp ∁ f g ≡ Id ∁) × (comp ∁ g f ≡ Id ∁))


iso : ∀ {i j} {∁ : Precategory {i} {j}}
      (a b : ob ∁)
      → Type j
iso {i} {j} {∁} a b = Σ[ f ∈ (hom ∁ a b) ] (isIso {i} {j} {∁} {a} {b} f)

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


isIso-is-prop : ∀ {i j} {∁ : Precategory {i} {j}} {a b : ob ∁} (f : hom ∁ a b)
             → isProp (isIso {i} {j} {∁} {a} {b} f)
isIso-is-prop {i} {j} {∁} {a} {b} f (g , η , ε) (g' , η' , ε') =  path-equiv-sigma
           (r-Id ∁ g ^ ∘ transport (λ X → comp ∁ X g ≡ g') (ε') ((ass ∁ _ _ _) ^ ∘ transport (λ X → comp ∁ g' X ≡ g') (η ^) (l-Id ∁ g') ) , path-equiv-prod ((hom-set ∁ _ _ _ _ _ η') , hom-set ∁ _ _ _ _ _ ε')) 

iso-is-set : ∀ {i j} {∁ : Precategory {i} {j}}
             (a b : ob ∁)
             → isSet (iso {_} {_} {∁} a b)
iso-is-set {_} {_} {∁} a b = prop-fibres-totalspace-set (hom-set ∁ a b) λ x → isIso-is-prop {_} {_} {∁} x

