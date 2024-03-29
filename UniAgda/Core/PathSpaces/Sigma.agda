{-# OPTIONS --without-K --safe --no-import-sorts #-}
module UniAgda.Core.PathSpaces.Sigma where

open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Functions
open import UniAgda.Core.Types.Identity
open import UniAgda.Core.Types.Sigma

open import UniAgda.Core.Homotopy
open import UniAgda.Core.Equivalences

-- * Paths in Sigma types

path-sigma : ∀ {i j} {A : Type i} {P : A → Type j}
             {w w' : Σ[ x ∈ A ] (P x)}
             → (w ≡ w') → (Σ[ p ∈ (pr₁ w ≡ pr₁ w') ] (transport P p (pr₂ w) ≡ (pr₂ w')))
path-sigma refl = refl , refl



path-equiv-sigma : ∀ {i j} {A : Type i} {P : A → Type j}
                   {w w' : Σ[ x ∈ A ] (P x)}
                   → (Σ[ p ∈ (pr₁ w ≡ pr₁ w') ] (transport P p (pr₂ w) ≡ (pr₂ w'))) → w ≡ w'
path-equiv-sigma {_} {_} {A} {P} {a , b} {.(pr₁ {_} {_} {A} {P} (a , b)) , .b} (refl , refl) = refl



private
  hom₃ : {i j : Level} {A : Type i} {P : A → Type j}
         {w w' : Σ[ x ∈ A ] (P x)}
         → path-sigma o path-equiv-sigma {_} {_} {A} {P} {w} {w'} ~ id
  hom₃ {i} {j} {A} {P} {w = _ , _} {w' = _ , _} (refl , refl) =  refl

  hom₄ : {i j : Level} {A : Type i} {P : A → Type j}
         {w w' : Σ[ x ∈ A ] (P x)}
         → path-equiv-sigma o path-sigma {_} {_} {A} {P} {w} {w'} ~ id
  hom₄ {i} {j} {A} {P} {a , b} .{a , b} refl = refl

thm2-7-2 : {i j : Level} {A : Type i} {P : A → Type j}
           {w w' : Σ[ x ∈ A ] (P x)}
           → (w ≡ w') ≃ (Σ[ p ∈ (pr₁ w ≡ pr₁ w') ] (transport P p (pr₂ w) ≡ (pr₂ w')))
thm2-7-2 {_} {_} {A} {P} {w} {w'} = equiv-adjointify (path-sigma , path-equiv-sigma , hom₃ , hom₄)

cor2-7-3 : {i j : Level} {A : Type i} {P : A → Type j}
           (z : Σ[ x ∈ A ] (P x))
           → z ≡ (pr₁ z , pr₂ z)
cor2-7-3 {i} {j} {A} {P} z = path-equiv-sigma {_} {_} {A} {P} {z} {pr₁ z , pr₂ z} (refl , refl)

-- * Paths in product types


path-equiv-prod : {i j : Level} {A : Type i} {B : Type j}
                  {x y : A × B}
                  → (pr₁ x ≡ pr₁ y) × (pr₂ x ≡ pr₂ y) → x ≡ y
path-equiv-prod {i} {j} {A} {B} {x = _ , _} {y = _ , _} (refl , refl) = refl

path-prod : {i j : Level} {A : Type i} {B : Type j}
            {x y : A × B}
            → x ≡ y → (pr₁ x ≡ pr₁ y) × (pr₂ x ≡ pr₂ y)
path-prod refl = refl , refl


private
  hom₁ : {i j : Level} {A : Type i} {B : Type j}
         {x y : A × B}
         → (path-equiv-prod o path-prod {i} {j} {A} {B} {x} {y}) ~ id
  hom₁ {x = _ , _} {y = _ , _} refl = refl

  hom₂ : {i j : Level} {A : Type i} {B : Type j}
         {x y : A × B}
         → (path-prod o path-equiv-prod {i} {j} {A} {B} {x} {y}) ~ id
  hom₂ {x = _ , _} {y = _ , _} (refl , refl) = refl


thm2-6-2 : {i j : Level} {A : Type i} {B : Type j}
           {x y : A × B}
           → isEquiv (path-prod {i} {j} {A} {B} {x} {y})
thm2-6-2 {x = _ , _} {y = _ , _} = isequiv-adjointify (path-equiv-prod , hom₂ , hom₁)

path-prod-equiv : {i j : Level} {A : Type i} {B : Type j}
            {x y : A × B}
            → (x ≡ y) ≃ ((pr₁ x ≡ pr₁ y) × (pr₂ x ≡ pr₂ y))
path-prod-equiv = path-prod , thm2-6-2
