{-# OPTIONS --without-K  --no-import-sorts #-}
module UniAgda.Categories.Examples.Set where


open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Functions
open import UniAgda.Core.Types.Identity
open import UniAgda.Core.Types.Sigma

open import UniAgda.Core.Equivalences

open import UniAgda.Core.Axioms

open import UniAgda.Core.SetsAndLogic.ContrPropSet1Type
open import UniAgda.Core.SetsAndLogic.Props
open import UniAgda.Core.SetsAndLogic.Sets
open import UniAgda.Core.SetsAndLogic.Equivalences

open import UniAgda.Core.PathSpaces.Sigma

open import UniAgda.Categories.Category
open Precategory
open Category

-- * SET is a precategory
-- We first show define SET as a precategory.

SET : ∀ i → Precategory (lsuc i) i
ob (SET i) = Set_ i
hom (SET i) a b = pr₁ a → pr₁ b
hom-set (SET i) a b = func-of-sets-is-set (pr₂ b)
Id (SET i) = id
comp (SET i) = _o_
IdL (SET i) f = refl
IdR (SET i) f = refl
Assoc (SET i) f g h = refl

-- * SET is a category
-- To show this, we need first prove a handful of results. The over
-- arching idea is that we can restrict the map "id-to-eqv" to just
-- those types that are sets, and use univalence at this level. First,
-- we prove univalence for sets.

UA-for-sets : ∀ {i} (X X' : Set_ i)
              → (X ≡ X') ≃ (pr₁ X ≃ pr₁ X')
UA-for-sets {i} (X₁ , a) (X₂ , b) =
  ((univalence ^ᵉ) oₑ id-equiv-to-prop-on-type X₁ X₂ isSet (λ A → isSet-is-prop A) a b) ^ᵉ


-- Next, we show that an isomorphism of sets is equivalent to a
-- quasi-equivalence of sets.

set-equiv-iso-qinv : ∀ {i} (A B : ob (SET i))
                     → (qequiv (pr₁ A) (pr₁ B)) ≃ (iso (SET i) A B)
set-equiv-iso-qinv {i} (X , a) (X' , b) = equiv-adjointify
  ((λ { (f , g , α , β) → f , (g , ((funext α) , (funext β)))}) ,
  (λ { (f , g , α , β) → f , (g , ((happly α) , (happly β)))}) ,
  (λ { (f , g , α , β) → path-equiv-sigma (refl ,
    transport (λ F → (g , funext (happly α) , F) ≡ (g , α , β)) (pr₁ (pr₂ happly-isEquiv) β ^)
      (transport (λ F → (g , F , id β) ≡ (g , α , β)) (pr₁ (pr₂ happly-isEquiv) α ^)
        refl))}) ,
  λ { (f , g , α , β) → path-equiv-sigma (refl ,
    (transport (λ F → (g , happly (funext α) , F) ≡ (g , α , β)) (pr₁ (pr₂ (pr₂ happly-isEquiv)) β ^)
      (transport (λ F → (g , F , id β) ≡ (g , α , β)) (pr₁ (pr₂ (pr₂ happly-isEquiv)) α ^)
        refl)))})


-- While in general it is not true that "qinv" is a proposition, it is
-- the case if we are working with sets.

qinv-of-sets-is-prop : ∀ {i} {A B : Set_ i}
                       (f : pr₁ A → pr₁ B)
                       → isProp (qinv f)
qinv-of-sets-is-prop {i} {X , a} {Y , b} f (g , α , β) (g' , α' , β') =
  path-equiv-sigma ((funext (λ y → β' (g y) ^ ∘ ap g' (α y))) ,
    path-equiv-sigma ((funextD (λ y → b _ _ _ _)) ,
      funextD λ x → a _ _ _ _))


-- The above two results give us an equivalence between paths and
-- isomorphisms in SET.

SET-id-equiv-iso : ∀ {i}
                   (A B : ob (SET i)) →
                   (A ≡ B) ≃ (iso (SET i) A B)
SET-id-equiv-iso {i} (X , a) (X' , b) =
  UA-for-sets (X , a) (X' , b) oₑ
  (equiv-fibres-to-equiv-sigma
    (λ f → props-equiv (isEquiv-is-prop f) (qinv-of-sets-is-prop {i} {X , a} {X' , b} f)
    isEquiv-to-qinv qinv-to-ishae) oₑ
  (set-equiv-iso-qinv (X , a) (X' , b)))


-- The map first map in this equivalence is then shown to be
-- id-to-iso, as required.

id-to-iso-equality : ∀ {i}
                     (A B : ob (SET i))
                     → pr₁ (SET-id-equiv-iso A B) ≡ id-to-iso (SET i) {A} {B}
id-to-iso-equality {i} (X , a) (X' , b) =
  funext λ { refl → path-equiv-sigma
    ((funext (λ x → refl)) ,
      isIso-is-prop (SET i) {(X , a)} {(X' , b)} _ _ _)}


-- We can then show that SET is indeed a category.

SET-is-category : ∀ {i}
                  → isCategory (SET i)
SET-is-category A B =
  transport (λ f → isEquiv f) (id-to-iso-equality A B)
    (pr₂ (SET-id-equiv-iso A B))

Set-Cat : ∀ {i}
          → Category (lsuc i) i
∁ (Set-Cat {i}) = SET i
univ (Set-Cat {i}) = SET-is-category
