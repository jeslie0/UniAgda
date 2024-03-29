-- Note - Loading all of the sigma type conversions causes a long
-- delay in loading this file. To save that, I will comment it out and
-- move it to another file at some point.
{-# OPTIONS --without-K --no-import-sorts #-}
module UniAgda.Categories.Category where

open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Functions
open import UniAgda.Core.Types.Sigma
open import UniAgda.Core.Types.Identity

open import UniAgda.Core.SetsAndLogic.ContrPropSet1Type
open import UniAgda.Core.SetsAndLogic.Props
open import UniAgda.Core.SetsAndLogic.Sets

open import UniAgda.Core.Homotopy
open import UniAgda.Core.Equivalences

open import UniAgda.Core.PathSpaces.Sigma
open import UniAgda.Core.PathAlgebra


open import UniAgda.Core.Axioms

-- * Precategories
-- We introduce precategories both as record and as a Σ type. The
-- reason for the double definition is that using record types with
-- this amount of data is much more organised and neater than working
-- with Σ types. However, proving results about categories is much
-- easier given the tools that we have developed for Σ types. We also
-- construct an equivalence between the two different types.

-- A precategory is defined as follows:

record Precategory (i j : Level) : Type (lsuc (i ⊔ j)) where
  eta-equality
  field
    ob : Type i
    hom : (a b : ob) → Type j
    hom-set : (a b : ob) → isSet (hom a b)
    Id : {a : ob} → (hom a a)
    comp : {a b c : ob} → (hom b c) → hom a b → hom a c
    IdL : {a b : ob} (f : hom a b) → comp f Id ≡ f
    IdR : {a b : ob} (f : hom a b) → comp Id f ≡ f
    Assoc : {a b c d : ob} (f : hom a b) (g : hom b c) (h : hom c d) → comp h (comp g f) ≡ comp (comp h g) f

  _<o>_ = comp

-- ** Isomorphisms
-- As isomorphisms are internal to a precategory, we define them in the record.


  isIso : {a b : ob} (f : hom a b) → Type j
  isIso {a} {b} f = Σ[ g ∈ (hom b a) ] ((comp f g ≡ Id) × (comp g f ≡ Id))

  iso : (a b : ob)
        → Type j
  iso a b = Σ[ f ∈ (hom a b) ] (isIso f)
  syntax iso a b = a ≅ b


-- The expected results about isomorphisms all hold, in particular
-- that "iso" is an equivalence relation.

  iso-refl : (a : ob)
                → iso a a
  iso-refl a =
    Id ,
    Id ,
    IdL Id ,
    IdR Id

  iso-sym : {a b : ob}
            → iso a b → iso b a
  iso-sym (f , g , x , y) =
    g ,
    f ,
    y ,
    x

  iso-trans : {a b c : ob}
              → iso a b → iso b c → iso a c
  iso-trans (f , g , x , y) (f' , g' , x' , y') =
    (comp f' f) ,
    (comp g g') ,
    (Assoc g' g _) ∘
      transport (λ z → comp z g' ≡ Id) (Assoc _ _ _) (
        transport (λ z → comp (comp f' z ) g' ≡ Id) (x ^) (
          transport (λ z → comp z g' ≡ Id) (IdL f' ^) x')) ,
    (Assoc _ g' g) ^ ∘
      transport (λ z → comp g z ≡ Id) (Assoc _ _ _ ^) (
        transport (λ z → comp g (comp z f) ≡ Id) (y' ^) (
          transport (λ z → comp g z ≡ Id) (IdR f ^) y))


-- Importantly, the type "isIso" is a proposition, which means that we
-- have a set of isomorphisms.

  isIso-is-prop : {a b : ob} (f : hom a b)
                  → isProp (isIso f)
  isIso-is-prop {a} {b} f (g , η , ε) (g' , η' , ε') =
                path-equiv-sigma
      (IdR g ^ ∘ transport (λ x → comp x g ≡ g') (ε') ((Assoc _ _ _) ^ ∘ transport (λ x → comp g' x ≡ g') (η ^) (IdL g')) ,
      path-equiv-prod ((hom-set _ _ _ _ _ η') , hom-set _ _ _ _ _ ε'))

  iso-is-set : (a b : ob)
               → isSet (iso a b)
  iso-is-set a b =
    prop-fibres-totalspace-set (hom-set a b) λ x → isIso-is-prop x


-- Any path in a precategory can be transformed into an isomorphism,
-- by induction. This function will be important when we deal with
-- Categories, rather than Precategories.

  id-to-iso : {a b : ob}
              → (a ≡ b) → (iso a b)
  id-to-iso refl =
    Id ,
    Id ,
    IdL Id ,
    IdR Id


-- ** Whiskering
-- Given an equality in a precategory, we can whisker with a morphism.

  precat-whiskerL : {x y z : ob} {f g : hom x y}
                       (p : f ≡ g) (h : hom y z)
                       → comp h f ≡ comp h g
  precat-whiskerL refl h = refl


  precat-whiskerR : {x y z : ob} {f g : hom y z}
                       (p : f ≡ g) (h : hom x y)
                       → comp f h ≡ comp g h
  precat-whiskerR refl h = refl

-- ** Sigma definition and equivalence
-- We now give the alternative definition as a Σ type:

Precategory-sig : ∀ (i j : Level) → Type (lsuc (i ⊔ j))
Precategory-sig i j =
  Σ[ ob ∈ (Type i) ] (
    Σ[ hom ∈ ((a b : ob) → Type j) ] (
      Σ[ hom-set ∈ ((a b : ob) → isSet (hom a b)) ] (
        Σ[ Id ∈ ({a : ob} → (hom a a)) ] (
          Σ[ comp ∈ ({a b c : ob} → (hom b c) → hom a b → hom a c) ] (
            Σ[ l-Id ∈ ({a b : ob} (f : hom a b) → comp f Id ≡ f) ] (
              Σ[ r-Id ∈ ({a b : ob} (f : hom a b) → comp Id f ≡ f) ] (
                {a b c d : ob} (f : hom a b) (g : hom b c) (h : hom c d) → comp h (comp g f) ≡ comp (comp h g) f)))))))


-- We have maps going between both types, as follows.

precategory-rec→sig : ∀ {i j}
                        → Precategory i j → Precategory-sig i j
precategory-rec→sig record { ob = ob ; hom = hom ; hom-set = hom-set ; Id = Id ; comp = comp ; IdL = IdL ; IdR = IdR ; Assoc = Assoc } =
  ob ,
  hom ,
  hom-set ,
  Id ,
  comp ,
  IdL ,
  IdR ,
  Assoc

precategory-sig→rec : ∀{i j}
                      → Precategory-sig i j → Precategory i j
precategory-sig→rec (ob , hom , hom-set , Id , comp , IdL , IdR , Assoc) =
  record
    { ob = ob
    ; hom = hom
    ; hom-set = hom-set
    ; Id = Id
    ; comp = comp
    ; IdL = IdL
    ; IdR = IdR
    ; Assoc = Assoc
    }


-- These functions both compose to give the identity.

precategory-sig→rec→sig : ∀ {i j}
                          (C : Precategory-sig i j)
                             → (precategory-rec→sig o precategory-sig→rec) C ≡ C
precategory-sig→rec→sig (ob , hom , hom-set , Id , comp , IdL , IdR , Assoc) =
  path-equiv-sigma (refl ,
    (path-equiv-sigma (refl ,
      (path-equiv-sigma (refl ,
        (path-equiv-sigma (refl ,
          (path-equiv-sigma (refl ,
            path-equiv-sigma (refl ,
              (path-equiv-sigma (refl ,
                refl))))))))))))

precategory-rec→sig→rec : ∀ {i j}
                          (C : Precategory i j)
                          → (precategory-sig→rec o precategory-rec→sig) C ≡ C
precategory-rec→sig→rec C = refl


-- The above is combined into a proof of equivalence.

Precategory-sig-equiv : ∀ {i j}
                        → Precategory-sig i j ≃ Precategory i j
Precategory-sig-equiv =
  equiv-adjointify
    (precategory-sig→rec ,
    precategory-rec→sig ,
    precategory-rec→sig→rec ,
    precategory-sig→rec→sig)


-- We open the precategory record so the rest of the file can use better notation.

open Precategory


-- ** Notation
-- It will be helpful to have some notation, to make it easier to
-- reason about categories. This notation is taken from the
-- [[https://github.com/agda/cubical/blob/master/Cubical/Categories/Category.agda][Cubical
-- Agda library]].

_[_,_] : ∀ {i j} (C : Precategory i j) → (x y : C .ob) → Type j
C [ x , y ] = C .hom x y

comp' : ∀ {i j} (∁ : Precategory i j) {x y z : ∁ .ob}
      (g : ∁ [ y , z ]) (f : ∁ [ x , y ])
      → ∁ [ x , z ]
comp' ∁ g f = ∁ .comp g f

infixr 15 comp'
syntax comp' C g f = g o⟨ C ⟩ f



-- * Categories
-- A category, in the sense of the HoTT book, is a precategory where
-- the map "id-to-iso" is an equivalence. These are sometimes referred
-- to as "univalent categories".


isCategory : ∀ {i j}
             (∁ : Precategory i j)
             → Type (i ⊔ j)
isCategory {i} {j} ∁ =
  (a b : ∁ .ob) → isEquiv (id-to-iso ∁ {a} {b})


-- We define a "category" to be a record of a precategory, with a
-- witness of "isCategory".

record Category (i j : Level) : Type (lsuc (i ⊔ j)) where
  eta-equality
  open Precategory
  field
    ∁ : Precategory i j
    univ : isCategory ∁

  module ∁ = Precategory ∁
                         
  iso-to-id : {a b : ∁ .ob}
          → (iso ∁ a b) → (a ≡ b)
  iso-to-id {a} {b} = pr₁ (univ a b)

  iso-id-equiv : {a b : ∁ .ob}
                 → (iso ∁ a b) ≃ (a ≡ b)
  iso-id-equiv {a} {b} =
    equiv-adjointify (iso-to-id , ((id-to-iso ∁) , (pr₁ (pr₂ (univ a b)) , pr₁ (pr₂ (pr₂ (univ a b))))))


-- There are some immediate results that we can prove about
-- categories. As they are "univalent", we would expect isomorphic
-- objects to be equal. This is the case and we prove them /in/ the
-- record.

  cat-iso-to-id : (a b : ∁ .ob) → iso ∁ a b → a ≡ b
  cat-iso-to-id a b x = pr₁ (univ a b) x


-- We also have that the type of objects of any category must be a
-- 1-type.

  cat-ob-is1type : is1type (∁ .ob)
  cat-ob-is1type a b = equiv-with-set (((id-to-iso ∁) , (univ a b)) ^ᵉ) (iso-is-set ∁ a b)


-- We also have the following few lemmas that hold in categories. The
-- first says that if we transport an isomorphism along "hom",
-- regarded as a type family, we conjugate with the carriers of the
-- isomorphisms.

  hom' : (∁ .ob × ∁ .ob) → Type j
  hom' (a , b) = hom ∁ a b

  lemma9-1-9 : {a a' b b' : ∁ .ob}
             (p : a ≡ a') (q : b ≡ b') (f : ∁ [ a , b ])
             → transport hom' (path-equiv-prod (p , q)) f ≡ ((pr₁ (id-to-iso ∁ q)) o⟨ ∁ ⟩ f) o⟨ ∁ ⟩ pr₁ (iso-sym ∁ (id-to-iso ∁ p))
  lemma9-1-9 refl refl f = IdR ∁ f ^ ∘ IdL ∁ (Id ∁ o⟨ ∁ ⟩ f ) ^

  id-to-iso^ : {a b : ∁ .ob}
                  (p : a ≡ b)
                  → id-to-iso ∁ (p ^) ≡ iso-sym ∁ (id-to-iso ∁ p)
  id-to-iso^ refl =
    path-equiv-sigma (refl ,
      (path-equiv-sigma (refl ,
        (path-equiv-sigma ((∁ .hom-set _ _ _ _ _ _) ,
          (∁ .hom-set _ _ _ _ _ _))))))

  id-to-iso-pq : {a b c : ∁ .ob}
                 (p : a ≡ b) (q : b ≡ c)
                 → id-to-iso ∁ (p ∘ q) ≡ iso-trans ∁ (id-to-iso ∁ p) (id-to-iso ∁ q)
  id-to-iso-pq refl refl =
    fibres-props-eq (isIso-is-prop ∁) _ _ (IdR ∁ (Id ∁) ^)

  iso-to-id-fe : {a b c : ∁ .ob}
                 (f : iso ∁ a b) (e : iso ∁ b c)
                 → iso-to-id (iso-trans ∁ f e) ≡ (iso-to-id f) ∘ (iso-to-id e)
  iso-to-id-fe {a} {b} {c} f e =
    equiv-types-eq
      iso-id-equiv
      (pr₁ (pr₂ (pr₂ (univ a c))) _ ∘
      (ap (λ Z → iso-trans ∁ f Z) (pr₁ (pr₂ (pr₂ (univ b c))) e ^) ∘
        ap (λ Z → iso-trans ∁ Z (id-to-iso ∁ (iso-to-id e))) (pr₁ (pr₂ (pr₂ (univ a b))) f ^)) ∘
      id-to-iso-pq (iso-to-id f) (iso-to-id e) ^)


-- ** Sigma definition and equivalence
-- We now give the Σ definition of a category.

Category-sig : (i j : Level)
                   → Type (lsuc (i ⊔ j))
Category-sig i j =
  Σ[ ∁ ∈ (Precategory i j) ] (
    isCategory ∁)


-- We have that the two different definitions are equivalent.

category-rec→sig : ∀ {i j}
                        → Category i j → Category-sig i j
category-rec→sig record { ∁ = ∁ ; univ = univ } = (∁ , univ)

category-sig→rec : ∀ {i j}
                   → Category-sig i j → Category i j
category-sig→rec (∁ , univ) = record { ∁ = ∁ ; univ = univ }

category-sig→rec→sig : ∀ {i j}
                       (C : Category-sig i j)
                       → (category-rec→sig o category-sig→rec) C ≡ C
category-sig→rec→sig (C , univ) =
  path-equiv-sigma (refl , refl)

category-rec→sig→rec : ∀ {i j}
                       (∁ : Category i j)
                       → (category-sig→rec o category-rec→sig) ∁ ≡ ∁
category-rec→sig→rec ∁ = refl


-- These are combined into an equivalence.

Category-sig-equiv : ∀ {i j}
                       → Category-sig i j ≃ Category i j
Category-sig-equiv =
  equiv-adjointify
    (category-sig→rec ,
    category-rec→sig ,
    category-rec→sig→rec ,
    category-sig→rec→sig)


-- * Opposite category
-- We define the opposite of a category and show that \((C
-- ^\text{op})^\text{op} = C\).

_^op : ∀ {i j} (C : Precategory i j)
       → Precategory i j
ob (C ^op) = C .ob
hom (C ^op) a b = C [ b , a ]
hom-set (C ^op) a b = C .hom-set b a
Id (C ^op) = C .Id
comp (C ^op) f g = g o⟨ C ⟩ f
IdL (C ^op) = C .IdR
IdR (C ^op) = C .IdL
Assoc (C ^op) f g h = Assoc C h g f ^


-- To show that "op" is an involution, we need to convert to Σ types,
-- \(p ^ ^\) is equal to p only up to a path. The proof uses refl on
-- every component except for associativity. Here, we need to unpack
-- using implicit and explicit function extensionalities, then give
-- the proof of  \(p^ ^ = p\).

op-involution : ∀ {i j}
                  (C : Precategory i j)
                  → (C ^op) ^op ≡ C
op-involution C = let module C = Precategory C in
  equiv-types-eq Precategory-sig-equiv
    (path-equiv-sigma (refl ,
      (path-equiv-sigma (refl ,
        (path-equiv-sigma (refl ,
          (path-equiv-sigma (refl ,
            (path-equiv-sigma (refl ,
              (path-equiv-sigma (refl ,
                (path-equiv-sigma (refl ,
                  implicit-funext λ a →
                  implicit-funext λ b →
                  implicit-funext λ c →
                  implicit-funext λ d →
                  funextD λ f →
                  funextD λ g →
                  funextD λ h →
                  p^^=p (C.Assoc f g h)))))))))))))))
