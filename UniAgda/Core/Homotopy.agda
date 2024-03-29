{-# OPTIONS --without-K --safe --no-import-sorts #-}
module UniAgda.Core.Homotopy where

open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Identity
open import UniAgda.Core.Types.Functions
open import UniAgda.Core.PathAlgebra

-- * Definition
-- We give the definition of a homotopy of functions, which states
-- that two functions are homotopic when they are equal pointwise.

-- Definition2.4.1
_~_ : ∀ {i j} {A : Type i} {P : A → Type j}
           (f g : (x : A) → P x)
           → Type (i ⊔ j)
_~_ {A = A} f g = (x : A) → (f x) ≡ (g x)
infix 6 _~_

-- * Homotopy forms an equivalence relation
-- Homotopy defines an equivalence relation on function types.

-- Lemma2.4.2
hrefl : ∀ {i j} {A : Type i} {P : A → Type j} {f : (x : A) → P x}
        → f ~ f
hrefl x = refl

hinv : ∀ {i j} {A : Type i} {P : A → Type j} {f g : (x : A) → P x}
       → (f ~ g)
       → (g ~ f)
hinv p x = p x ^
_^ʰ = hinv

hconcatenation : ∀ {i j} {A : Type i} {P : A → Type j} {f g h : (x : A) → P x}
                 → (f ~ g) → (g ~ h)
                 → (f ~ h)
hconcatenation p q x = p x ∘ q x
_∘ₕ_ = hconcatenation


-- * Homotopy is natural
-- Homotopies act like natural transformations.

-- Lemma2.4.3
homotopy-natural : ∀ {i j} {A : Type i} {B : Type j} {x y : A} {f g : A → B}
                   (H : f ~ g) (p : x ≡ y)
                   → (H x ∘ (ap g p)) ≡ (ap f p ∘ H y)
homotopy-natural {x = x} H refl = p-refl (H x) ∘ refl-p (H x)

-- This leads to the following useful result:
-- Corollary2.4.4
cor2-4-4 : ∀ {i} {A : Type i}
           (f : A → A) (H : f ~ id) (x : A)
           → (H (f x)) ≡ (ap f (H x))
cor2-4-4 {i} {A} f H x =
  (p-refl (H (f x)) ^) ∘
  ((ap (λ p → H (f x) ∘ p) (ap-idp-p^ (H x)) ^) ∘
    ((ass-r (H (f x)) (ap id (H x)) (H x ^)) ∘
      (ap (λ p → p ∘ (H x ^)) (homotopy-natural {_} {_} {A} {A} {f x} {x} {f} {id} H (H x)) ∘
        (ass-l (ap f (H x)) (H x) (H x ^) ∘ (ap (λ p → (ap f (H x)) ∘ p) (pp^ (H x)) ∘
         p-refl (ap f (H x)))))))


-- * Whiskering
-- We can whisker homotopies and homotopies.
whisker-r : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} {f g : A → B}
          (H : f ~ g) (h : C → A)
          → f o h ~ g o h
whisker-r H h x = H (h x)


whisker-l : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} {f g : A → B}
          (H : f ~ g) (h : B → C)
          → h o f ~ h o g
whisker-l H h x = ap h (H x)

-- * Homotopy algebra
-- We include some results for manipulating homotopies.
hass-l : ∀ {i j} {A : Type i} {B : A → Type j} {f₁ f₂ f₃ f₄ : (x : A) → B x}
         (H : f₁ ~ f₂) (G : f₂ ~ f₃) (F : f₃ ~ f₄)
         → (H ∘ₕ G) ∘ₕ F ~ H ∘ₕ (G ∘ₕ F)
hass-l H G F x = ass-l (H x) (G x) (F x)

hass-r : ∀ {i j} {A : Type i} {B : A → Type j} {f₁ f₂ f₃ f₄ : (x : A) → B x}
         (H : f₁ ~ f₂) (G : f₂ ~ f₃) (F : f₃ ~ f₄)
         → H ∘ₕ (G ∘ₕ F) ~ (H ∘ₕ  G) ∘ₕ F
hass-r H G F x = ass-r (H x) (G x) (F x)

HH^ : ∀ {i j} {A : Type i} {B : Type j} {f g : A → B}
      (H : f ~ g)
      → H ∘ₕ (H ^ʰ) ~ hrefl
HH^ H x = pp^ (H x)

H^H : ∀ {i j} {A : Type i} {B : A → Type j} {f g : (x : A) → B x}
      (H : f ~ g)
      → (H ^ʰ) ∘ₕ (H) ~ hrefl
H^H H x = p^p (H x)

H-refl : ∀ {i j} {A : Type i} {B : A → Type j} {f g : (x : A) → B x}
        (H : f ~ g)
        → (H ∘ₕ hrefl) ~ H
H-refl H x = p-refl (H x)

refl-H : ∀ {i j} {A : Type i} {B : A → Type j} {f g : (x : A) → B x}
        (H : f ~ g)
        → (hrefl ∘ₕ H) ~ H
refl-H H x = refl-p (H x)

-- Cancelling h-inverses

H^^~H : ∀ {i j} {A : Type i} {B : A → Type j} {f g : (x : A) → B x}
        (H : f ~ g)
        → (H ^ʰ) ^ʰ ~ H
H^^~H H x = p^^=p (H x)

H-H^G~G : ∀ {i j} {A : Type i} {B : A → Type j} {f g h : (x : A) → B x}
          (H : f ~ g) (G : f ~ h)
          → H ∘ₕ ((H ^ʰ) ∘ₕ G) ~ G
H-H^G~G H G x = p-p^q=q (H x) (G x)

HH^-G~G : ∀ {i j} {A : Type i} {B : A → Type j} {f g h : (x : A) → B x}
          (H : f ~ g) (G : f ~ h)
          → (H ∘ₕ (H ^ʰ)) ∘ₕ G ~ G
HH^-G~G H G x = pp^-q=q (H x) (G x)

H^-H^G~G : ∀ {i j} {A : Type i} {B : A → Type j} {f g h : (x : A) → B x}
          (H : f ~ g) (G : g ~ h)
          → (H ^ʰ) ∘ₕ (H ∘ₕ G) ~ G
H^-H^G~G H G x = p^-pq=q (H x) (G x)

H^H-G~G : ∀ {i j} {A : Type i} {B : A → Type j} {f g h : (x : A) → B x}
          (H : f ~ g) (G : g ~ h)
          → ((H ^ʰ) ∘ₕ H) ∘ₕ G ~ G
H^H-G~G H G x = p^p-q=q (H x) (G x)

-- Composites with hrefl

Hrefl-G~HG : ∀ {i j} {A : Type i} {B : A → Type j} {f g h : (x : A) → B x}
          (H : f ~ g) (G : g ~ h)
          → (H ∘ₕ hrefl) ∘ₕ G ~ H ∘ₕ G
Hrefl-G~HG H G x = prefl-q=pq (H x) (G x)

H-reflG~HG : ∀ {i j} {A : Type i} {B : A → Type j} {f g h : (x : A) → B x}
          (H : f ~ g) (G : g ~ h)
          → H ∘ₕ (hrefl ∘ₕ G) ~ H ∘ₕ G
H-reflG~HG H G x = refl

-- Moving inverses about

HG~K-to-G~H^K : ∀ {i j} {A : Type i} {B : A → Type j} {f g h : (x : A) → B x}
          (H : f ~ g) (G : g ~ h) (K : f ~ h)
          → H ∘ₕ G ~ K → G ~ (H ^ʰ) ∘ₕ K
HG~K-to-G~H^K H G K x x₁ = pq=r-to-q=p^r (H x₁) (G x₁) (K x₁) (x x₁)

HG~K-to-H~KG^ : ∀ {i j} {A : Type i} {B : A → Type j} {f g h : (x : A) → B x}
          (H : f ~ g) (G : g ~ h) (K : f ~ h)
          → H ∘ₕ G ~ K → H ~ K ∘ₕ (G ^ʰ)
HG~K-to-H~KG^ H G K x x₁ = pq=r-to-p=rq^ (H x₁) (G x₁) (K x₁) (x x₁)

-- Inverses and concatenation

HG-^-to-G^H^ : ∀ {i j} {A : Type i} {B : A → Type j} {f g h : (x : A) → B x}
          (H : f ~ g) (G : g ~ h)
          → (H ∘ₕ G) ^ʰ ~ (G ^ʰ) ∘ₕ (H ^ʰ)
HG-^-to-G^H^ H G x = pq-^-to-q^p^ (H x) (G x)
