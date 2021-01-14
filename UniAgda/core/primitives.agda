{-

This file defines the main type formers that we use, along with some basic and frequently used results about them.

-}

{-# OPTIONS --without-K --no-import-sorts --safe #-}
module UniAgda.core.primitives where

{-
Universes
-}

-- copying from Cubical
open import Agda.Primitive public
  using    ( Level ; lzero ; lsuc ; _⊔_)
  renaming ( Set  to Type
           ; Setω to Typeω )

data raise (l : Level) {l1 : Level} (A : Type l1) : Type (l1 ⊔ l) where
  map-raise : A → raise l A

map-inv-raise :
  {l l1 : Level} {A : Type l1} → raise l A → A
map-inv-raise (map-raise x) = x


{-
Function basics
-}

composition : {i₁ i₂ i₃ : Level} {A : Type i₁} {B : Type i₂} {C : Type i₃}
              (g : B → C) (f : A → B)
              → A → C
composition g f a = g (f a)
_o_ = composition
infixr 9 _o_

id : {i : Level} {A : Type i}
     → A → A
id a = a


{-
Identity Types
-}

data _≡_ {i : Level} {A : Type i} (x : A) : A → Type i where
  refl : x ≡ x
infix 5 _≡_
_==_ = _≡_
{-# BUILTIN EQUALITY _≡_ #-}

-- Path induction
bpath-ind : {i j : Level} {A : Type i}
            (a : A) (C : (x : A) → a ≡ x → Type j) (c : C a refl)
            → (x : A) (p : a ≡ x) → C x p
bpath-ind a C c .a refl = c

path-ind : {i j : Level} {A : Type i}
           (C : (x y : A) → x ≡ y → Type j) (c : (x : A) → C x x refl)
         → (a b : A) → (p : a ≡ b) → C a b p
path-ind C c x .x refl = c x

-- Groupoid structure

_^ : {i : Level} {A : Type i} {x y : A}
     (p : x ≡ y)
     → y ≡ x
refl ^ = refl
infix 30 _^

_∘_ : {i : Level} {A : Type i} {x y z : A}
                (p : x ≡ y) (q : y ≡ z)
                → x ≡ z
_∘_ refl q = q
concatenation = _∘_
infixr 20 _∘_

horizontal-comp : {i : Level} {A : Type i} {a b c : A} {p q : a ≡ b} {s r : b ≡ c}
                  (α : p ≡ q) (β : r ≡ s)
                  → (p ∘ r) ≡ (q ∘ s)
horizontal-comp refl refl = refl
_⋆_ = horizontal-comp


-- ap definition

ap : {i j : Level} {A : Type i} {B : Type j} {x y : A}
     (f : A → B) (p : x ≡ y)
     → (f x ≡ f y)
ap f refl = refl

-- Transport
transport : {i j : Level} {A : Type i} {x y : A}
            (P : A → Type j) (p : x ≡ y)
            → P x → P y
transport P refl = λ x → x

_#_ : {i j : Level }{A : Type i} {x y : A} {P : A → Type j}
      (p : x ≡ y) → P x
      → P y
_#_ {_} {_}{A} {x} {y} {P} p a = transport P p a
infixr 29 _#_

-- Dependent ap

apD : {i j : Level }{A : Type i} {x y : A} {P : A → Type j} (f : (x : A) → P x) → (p : x ≡ y) → (transport P p (f x)) ≡ (f y)
apD f refl = refl


{-
Sigma types
-}


-- record Σ {i j : Level} (A : Type i) (B : A → Type j) : Type (i ⊔ j) where
--   constructor _,_
--   field
--     pr₁ : A
--     pr₂ : B pr₁

-- open Σ public

data Σ {i j : Level} (A : Type i) (B : A → Type j) : Type (i ⊔ j) where
  _,_ : (a : A) → (b : B a) → Σ A B

pr₁ : {i j : Level} {A : Type i} {B : A → Type j} → Σ A B → A
pr₁ (a , b) = a

pr₂ : {i j : Level} {A : Type i} {B : A → Type j} → (p : Σ A B) → B(pr₁ p)
pr₂ (a , b) = b

syntax Σ A (λ x → B) = Σ[ x ∈ A ] B
infixr 4 _,_

pr₃ : {i₁ i₂ i₃ : Level}
      {A : Type i₁} {B : A → Type i₂} {C : (x : A) (y : B x) → Type i₃}
      → (t : Σ[ x ∈ A ] (Σ[ y ∈ (B x)] (C x y))) → C (pr₁ t) (pr₁(pr₂ t))
pr₃ (a , (b , c)) = c


_×_ : {i j : Level} (A : Type i) (B : Type j) → Type (i ⊔ j)
A × B = Σ A (λ _ → B)


_↔_ : ∀ {i j} (A : Type i) (B : Type j) → Type (i ⊔ j)
A ↔ B = (A → B) × (B → A)

{-
Coproduct type
-}

data _+_ {i j : Level} (A : Type i) (B : Type j) : Type (i ⊔ j) where
  inl : A → A + B
  inr : B → A + B

{-
W-types
-}

data W {i j : Level} (A : Type i) (B : A → Type j) : Type (i ⊔ j) where
  sup : (a : A) → (B a → W A B) → W A B

syntax W A (λ x → B) = W[ x ∈ A ] B


{-
Unit Type
-}

data Unit : Type lzero where
  tt : Unit


{-
Empty Type
-}

data Empty : Type lzero where

¬ : {i : Level}
    (A : Type i)
    → Type i
¬ A = A → Empty
infix 50 ¬


{-
Bool
-}

data Bool : Type lzero where
  true : Bool
  false : Bool

{-# BUILTIN BOOL Bool #-}
{-# BUILTIN TRUE true #-}
{-# BUILTIN FALSE false #-}

swap : Bool → Bool
swap true = false
swap false = true

rec₂ : {i : Level} (C : Type i)
       → C → C → Bool → C
rec₂ C c₀ c₁ true = c₁
rec₂ C c₀ c₁ false = c₀

{-
Natural numbers type
-}

data ℕ  : Type lzero where
  zero : ℕ
  suc : ℕ -> ℕ
{-# BUILTIN NATURAL ℕ #-}

plus : ℕ → ℕ → ℕ
plus zero m = m
plus (suc n) m = suc (plus n m)
{-# BUILTIN NATPLUS plus #-}

minus : ℕ → ℕ → ℕ
minus n zero = n
minus zero (suc m) = zero
minus (suc n) (suc m) = minus n m
{-# BUILTIN NATMINUS minus #-}

times : ℕ → ℕ → ℕ
times zero m = zero
times (suc n) m = plus (times n m) m
{-# BUILTIN NATTIMES times #-}

power : ℕ → ℕ → ℕ
power n zero = suc zero
power n (suc m) = times (power n m) n

