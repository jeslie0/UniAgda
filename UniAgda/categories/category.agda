{-# OPTIONS --without-K  #-}
module UniAgda.categories.category where

open import UniAgda.categories.precat public

id-to-iso : ∀ {i j} (∁ : Precategory {i} {j}) {a b : ob ∁}
            → (a ≡ b) → (iso {i} {j} {∁} a b)
id-to-iso {i} {j} ∁ refl = (Id ∁) , ((Id ∁) , (l-Id ∁ (Id ∁) , r-Id ∁ (Id ∁)))

-- record isCategory {i j} (∁ : Precategory {i} {j}) : Type (lsuc (i ⊔ j)) where
--   field
--     univ : (a b : ob ∁) → isEquiv (id-to-iso {i} {j} ∁ {a} {b})

-- open isCategory public

isCategory : ∀ {i j} → (∁ : Precategory {i} {j}) → Type (_)
isCategory {i} {j} ∁ = (a b : ob ∁) → isEquiv (id-to-iso {i} {j} ∁ {a} {b})
univ = isCategory
Category : ∀ {i j} → Type _
Category {i} {j} = Σ[ C ∈ (Precategory {i} {j}) ] (isCategory C)

-- univ = ∀ {i j} {C : Precategory {i} {j}} (P : )

Cat-iso-to-id : ∀ {i j} {∁ : Precategory {i} {j}} {H : isCategory ∁}
        → (a b : ob ∁) → iso {_} {_} {∁} a b → a ≡ b
Cat-iso-to-id {i} {j} {∁} {H} a b x = pr₁ (H a b) x

cat-ob-is1type : ∀ {i j} {∁ : Precategory {i} {j}} {H : isCategory ∁} → is1type (ob ∁)
cat-ob-is1type {i} {j} {∁} {H} a b = equiv-with-set (((id-to-iso ∁) , (H a b)) ^ᵉ) (iso-is-set {_} {_} {∁} a b)

