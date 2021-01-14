{-# OPTIONS --without-K #-}
module UniAgda.e-cat.precategory where

open import UniAgda.core.CORE public

record Precategory (i j : Level) : Type (lsuc (i ⊔ j)) where
  eta-equality {- This is needed for opop -}
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
open Precategory

_[_,_] : ∀ {i j} (C : Precategory i j) → (x y : C .ob) → Type j
C [ x , y ] = C .hom x y

seq : ∀ {i j} (∁ : Precategory i j) {x y z : ∁ .ob} (f : ∁ [ x , y ]) (g : ∁ [ y , z ]) → ∁ [ x , z ]
seq ∁ f g = ∁ .comp g f

infix 15 seq
syntax seq C f g = f ∙⟨ C ⟩ g


{- Sigma definition -}

Precategory-Sig : ∀ (i j : Level) → Type (_)
Precategory-Sig i j =
  Σ[ ob ∈ (Type i) ] (
    Σ[ hom ∈ ((a b : ob) → Type j) ] (
      Σ[ hom-set ∈ ((a b : ob) → isSet (hom a b)) ] (
        Σ[ Id ∈ ({a : ob} → (hom a a)) ] (
          Σ[ comp ∈ ({a b c : ob} → (hom b c) → hom a b → hom a c) ] (
            Σ[ l-Id ∈ ({a b : ob} (f : hom a b) → comp f Id ≡ f) ] (
              Σ[ r-Id ∈ ({a b : ob} (f : hom a b) → comp Id f ≡ f) ] (
                {a b c d : ob} (f : hom a b) (g : hom b c) (h : hom c d) → comp h (comp g f) ≡ comp (comp h g) f)))))))

postulate
  Precategory-Sig-eq : ∀ {i j} → Precategory-Sig i j ≡ Precategory i j



{- Defining the opposite category -}
_^op : ∀ {i j} (∁ : Precategory i j)
       → Precategory i j
ob (∁ ^op) = ∁ .ob
hom (∁ ^op) a b = ∁ .hom b a
hom-set (∁ ^op) a b = ∁ .hom-set b a
Id (∁ ^op) = ∁ .Id
comp (∁ ^op) f g = ∁ .comp g f
l-Id (∁ ^op) = ∁ .r-Id
r-Id (∁ ^op) = ∁ .l-Id
ass (∁ ^op) f g h = ∁ .ass h g f ^


-- op-involution : ∀ {i j} (∁ : Precategory i j)
--                 → (∁ ^op) ^op ≡ ∁
-- op-involution = {!thm2-11-1!}




isCategory : ∀ {i j} → (∁ : Precategory i j) → Type (_)
isCategory {i} {j} ∁ = let module ∁ = Precategory ∁ in
  (a b : ∁.ob) → isEquiv (∁.id-to-iso {a} {b})

record Category {i j : Level} : Type (lsuc (i ⊔ j)) where
  no-eta-equality
  field
    ∁ : Precategory i j
    univ : isCategory ∁


  cat-iso-to-id : (a b : Precategory.ob ∁) → Precategory.iso ∁ a b → a ≡ b
  cat-iso-to-id a b x = pr₁ (univ a b) x

  cat-ob-is1type : is1type (Precategory.ob ∁)
  cat-ob-is1type a b = equiv-with-set (((Precategory.id-to-iso ∁) , (univ a b)) ^ᵉ) (Precategory.iso-is-set ∁ a b)

open Category
