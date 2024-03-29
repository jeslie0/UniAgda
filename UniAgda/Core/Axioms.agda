{-# OPTIONS --without-K --no-import-sorts #-}
module UniAgda.Core.Axioms where

open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Functions
open import UniAgda.Core.Types.Identity
open import UniAgda.Core.Types.Sigma

open import UniAgda.Core.PathSpaces.Sigma
open import UniAgda.Core.Homotopy
open import UniAgda.Core.Equivalences
open import UniAgda.Core.SetsAndLogic.ContrPropSet1Type

-- * Function Extensionality
-- Function Extensionality states that two functions are equal exactly
-- when they are homotopic. This isn't provable and needs to be given
-- as an axiom.

happly : {i j : Level} {A : Type i} {B : Type j} {f g : A → B}
         → f ≡ g → f ~ g
happly refl = hrefl

postulate
  happly-isEquiv : {i j : Level} {A : Type i} {B : Type j} {f g : A → B}
                   → isEquiv (happly {i} {j} {A} {B} {f} {g})

ax2-9-3 = happly-isEquiv
-- abstract
funext : {i j : Level} {A : Type i} {B : Type j} {f g : A → B}
         → f ~ g → f ≡ g
funext = pr₁ ax2-9-3

funext-equiv : {i j : Level} {A : Type i} {B : Type j} {f g : A → B}
                 → (f ≡ g) ≃ (f ~ g)
funext-equiv = happly , ax2-9-3

funext-happly-to-id : {i j : Level} {A : Type i} {B : Type j} {f g : A → B}
                       → funext o happly {i} {j} {A} {B} {f} {g} ~ id
funext-happly-to-id = pr₁ ( (pr₂ happly-isEquiv))

happly-funext-to-id : {i j : Level} {A : Type i} {B : Type j} {f g : A → B}
                      → happly o funext {i} {j} {A} {B} {f} {g} ~ id
happly-funext-to-id = (pr₁ (pr₂ (pr₂ happly-isEquiv)))

-- ** Dependant Function Extensionality
-- We also postulate a dependant version of function extensionality.

happlyD : {i j : Level} {A : Type i} {B : A → Type j} {f g : (x : A) → B x}
          → f ≡ g → f ~ g
happlyD refl x₁ = refl

postulate
  funextD : {i j : Level} {A : Type i} {B : A → Type j} {f g : (x : A) → B x}
          → (f ~ g) → f ≡ g

postulate
  happlyD-funextD~Id : {i j : Level} {A : Type i} {B : A → Type j} {f g : (x : A) → B x}
                            → happlyD {i} {j} {A} {B} {f} {g} o funextD ~ id

postulate
  funextD-happlyD~Id : {i j : Level} {A : Type i} {B : A → Type j} {f g : (x : A) → B x}
                            → funextD {i} {j} {A} {B} {f} {g} o happlyD ~ id

happlyD-isEquiv : {i j : Level} {A : Type i} {B : A → Type j} {f g : (x : A) → B x}
                    → isEquiv (happlyD {i} {j} {A} {B} {f} {g})
happlyD-isEquiv = isequiv-adjointify (funextD , happlyD-funextD~Id , funextD-happlyD~Id)

funextD-equiv : {i j : Level} {A : Type i} {B : A → Type j} {f g : (x : A) → B x}
                → (f ≡ g) ≃ (f ~ g)
funextD-equiv = happlyD , happlyD-isEquiv

-- ** Implicit Function Extensionality
-- At times we will need to use a version of function extensionality
-- that works with implicit arguments. We introduce this here.
private
  implicit-eval : ∀ {i j} {A : Type i} {B : A → Type j}
                  → ((x : A) → B x) → {x : A} → B x
  implicit-eval f {x} = f x

implicit-funext : ∀ {i j} {A : Type i} {B : A → Type j} {f g : {x : A} → B x}
                  (H : (x : A) → f {x} ≡ g {x})
                  → (λ {x} → f {x}) ≡ (λ {x} → g {x})
implicit-funext {f = f} {g = g} H = ap implicit-eval (funextD {f = λ x → f{x}} {g = λ x → g{x}} H)

postulate
  implicit-funext-is-equiv : {i j : Level} {A : Type i} {B : A → Type j} {f g : {x : A} → B x}
                           → isEquiv (implicit-funext {i} {j} {A} {B} {f} {g})

implicit-funext-equiv :  {i j : Level} {A : Type i} {B : A → Type j} {f g : {x : A} → B x}
                            →  ((x : A) → f {x} ≡ g {x}) ≃ ( (λ {x} → f {x}) ≡ (λ {x} → g {x}))
implicit-funext-equiv = implicit-funext , implicit-funext-is-equiv

implicit-happly : {i j : Level} {A : Type i} {B : A → Type j} {f g : {x : A} → B x}
                         → (λ {a} → f {a}) ≡ (λ {a} → g {a})
                         → ((x : A) → f {x} ≡ g {x})
implicit-happly {i} {j} {A} {B} {f} {g} = pr₁ (implicit-funext-is-equiv {i} {j} {A} {B} {f} {g})

-- ** Transport into Π types
-- Result 2.9.4
transport-into-func : ∀ {i j k} {X : Type i} {x₁ x₂ : X}
                      (A : X → Type j)
                      (B : X → Type k)
                      (p : x₁ ≡ x₂)
                      (f : A x₁ → B x₁)
                      → transport (λ x → A x → B x) p f ≡ λ x → transport B p (f (transport A (p ^) x))
transport-into-func A B refl f = refl

-- Result 2.9.5
transport-into-Pi : ∀ {i j k} {X : Type i} {x₁ x₂ : X}
                    (A : X → Type j)
                    (B : (x : X) → A x → Type k)
                    (p : x₁ ≡ x₂)
                    (f : (a : A x₁) → B x₁ a)
                    → (a : A x₂)
                    → ((transport (λ x → (a' : A x) → B x a') p f) a) ≡ transport (λ w → B (pr₁ w) (pr₂ w)) ((path-equiv-sigma {i} {j} {X} {A} {x₂ , a} {x₁ , transport A (p ^) a} ((p ^) , refl)) ^) (f (transport A (p ^) a))
transport-into-Pi A B refl f a = refl


-- * Univalence
-- The Univalence Axiom is the heart of Homotopy Type Theory. It
-- states that equality of types is equivalent to equivalence of
-- types. This captures the notion of two objects being equal when
-- they're isomorphic. In particular, it states that a certain
-- function is an equivalence.

id-to-eqv : {i : Level} {A B : Type i}
            → A ≡ B → A ≃ B
id-to-eqv refl = erefl

postulate
  ua : {i : Level} {A B : Type i}
       → A ≃ B → A ≡ B

private
  postulate
    hom₁ : {i : Level} {A B : Type i}
           → id-to-eqv o ua {i} {A} {B} ~ id

    hom₂ : {i : Level} {A B : Type i}
           → ua o id-to-eqv {i} {A} {B} ~ id

ax2-10-3 : {i : Level} {A B : Type i}
           → isEquiv (id-to-eqv {i} {A} {B})
ax2-10-3 = isequiv-adjointify (ua , hom₁ , hom₂)

univalence : {i : Level} {A B : Type i}
             → (A ≡ B) ≃ (A ≃ B)
univalence = id-to-eqv , ax2-10-3

-- ** Computation Rules
-- Univalence satisfies the following rules.

ua-cmpt : {i : Level} {A B : Type i} {f : A ≃ B} {x : A}
       → e-ap (id-to-eqv (ua f)) x ≡ e-ap f x
ua-cmpt {i} {A} {B} {f} {x} = ap (λ f → e-ap {i} {i} {A} {B} f x) (hom₁ f)

ua-η : {i : Level} {A B : Type i}
       (p : A ≡ B)
       → p ≡ ua (id-to-eqv p)
ua-η p = hom₂ p ^


id-to-eqv-refl : {i : Level} {A : Type i}
               → id-to-eqv refl ≡ erefl {i} {A}
id-to-eqv-refl = refl

ua-id : {i : Level} {A : Type i}
      → refl ≡ ua {i} {A} {A} erefl
ua-id {i} {A} = (pr₁ (pr₂ ax2-10-3) refl) ^ ∘ ap ua (id-to-eqv-refl {i} {A})

-- * Propositional Resizing

Prop-resizing-map : {i : Level}
                    → (Prop_ i) → Prop_ (lsuc i)
Prop-resizing-map (A , X) = (raise _ A) , (λ { (map-raise x) (map-raise x₁) → ap (map-raise) (X x x₁) })

postulate
  Prop-resizing-equiv : {i : Level}
                  → isEquiv (Prop-resizing-map {i})

abstract
  Prop-resizing : {i : Level}
                    → Prop_ (lsuc i) → Prop_ i
  Prop-resizing {i} = pr₁ Prop-resizing-equiv
