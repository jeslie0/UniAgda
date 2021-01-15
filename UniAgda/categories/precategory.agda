{-# OPTIONS --without-K  #-}
module UniAgda.categories.precategory where

open import UniAgda.core.CORE public

record Precategory {i j} : Type (lsuc (i ⊔ j)) where
  eta-equality
  field
    ob : Type i
    hom : (a b : ob) → Type j
    hom-set : (a b : ob) → isSet (hom a b)
    Id : {a : ob} → (hom a a)
    comp : {a b c : ob} → (hom b c) → hom a b → hom a c
    l-Id : {a b : ob} (f : hom a b) → comp f Id ≡ f
    r-Id : {a b : ob} (f : hom a b) → comp Id f ≡ f
    ass : {a b c d : ob} (f : hom a b) (g : hom b c) (h : hom c d) → comp h (comp g f) ≡ comp (comp h g) f

  _$o_ = comp

  isIso : {a b : ob} (f : hom a b) → Type j
  isIso {a} {b} f = Σ[ g ∈ (hom b a) ] ((f $o g ≡ Id) × (g $o f ≡ Id))

  iso : (a b : ob)
        → Type j
  iso a b = Σ[ f ∈ (hom a b) ] (isIso f)

  -- "iso" is an equivalence relation 


  iso-refl : (a : ob)
             → iso a a
  iso-refl a =
    Id ,
    Id ,
    l-Id Id ,
    r-Id Id


  iso-sym : (a b : ob)
            → iso a b → iso b a
  iso-sym a b (f , g , x , y) =
    g ,
    f ,
    y ,
    x

  iso-trans : (a b c : ob)
              → iso a b → iso b c → iso a c
  iso-trans a b c (f , g , x , y) (f' , g' , x' , y') =
    (comp f' f) ,
    (comp g g') ,
    (ass g' g _) ∘
      transport (λ z → comp z g' ≡ Id) (ass _ _ _) (
        transport (λ z → comp (comp f' z ) g' ≡ Id) (x ^) (
          transport (λ z → comp z g' ≡ Id) (l-Id f' ^) x')) ,
    (ass _ g' g) ^ ∘
      transport (λ z → comp g z ≡ Id) (ass _ _ _ ^) (
        transport (λ z → comp g (comp z f) ≡ Id) (y' ^) (
          transport (λ z → comp g z ≡ Id) (r-Id f ^) y))


  isiso-is-prop : {a b : ob} (f : hom a b)
                → isProp (isIso f)
  isiso-is-prop {a} {b} f (g , η , ε) (g' , η' , ε') =
    path-equiv-sigma
      (r-Id g ^ ∘ transport (λ x → comp x g ≡ g') (ε') ((ass _ _ _) ^ ∘ transport (λ x → comp g' x ≡ g') (η ^) (l-Id g')) ,
      path-equiv-prod ((hom-set _ _ _ _ _ η') , hom-set _ _ _ _ _ ε'))


  iso-is-set : (a b : ob)
               → isSet (iso a b)
  iso-is-set a b =
    prop-fibres-totalspace-set (hom-set a b) λ x → isiso-is-prop x


  id-to-iso : {a b : ob}
              → (a ≡ b) → (iso a b)
  id-to-iso refl =
    Id ,
    Id ,
    l-Id Id ,
    r-Id Id 
-- open Precategory public

{- Defining the opposite category -}
_^op : ∀ {i j} (∁ : Precategory {i} {j})
       → Precategory {i} {j}
_^op {i} {j} ∁ = let module ∁ = Precategory ∁ in record
                                                 { ob = ∁.ob
                                                 ; hom = λ a b → ∁.hom b a
                                                 ; hom-set = λ a b → ∁.hom-set b a
                                                 ; Id = ∁.Id
                                                 ; comp = λ f g → g ∁.$o f
                                                 ; l-Id = ∁.r-Id
                                                 ; r-Id = ∁.l-Id
                                                 ; ass = λ f g h → ∁.ass h g f ^
                                                 }

-- ob (_^op {i} {j} ∁) = ob ∁
-- hom (_^op {i} {j} ∁) a b = hom ∁ b a
-- hom-set (_^op {i} {j} ∁) a b = hom-set ∁ b a
-- Id (_^op {i} {j} ∁) = Id ∁
-- comp (_^op {i} {j} ∁) f g = comp ∁ g f
-- l-Id (_^op {i} {j} ∁) f = r-Id ∁ f
-- r-Id (_^op {i} {j} ∁) f = l-Id ∁ f
-- ass (_^op {i} {j} ∁) f g h = ass ∁ h g f ^

