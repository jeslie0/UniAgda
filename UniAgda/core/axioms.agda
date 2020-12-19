{-# OPTIONS --without-K #-}
module UniAgda.core.axioms where

open import UniAgda.core.equivalences public

{- Function extensionality -}

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
                       → funext o happly {i} {j} {A} {B} {f} {g} ≡ id
funext-happly-to-id = funext (pr₁ ( (pr₂ happly-isEquiv)))

happly-funext-to-id : {i j : Level} {A : Type i} {B : Type j} {f g : A → B} 
                      → happly o funext {i} {j} {A} {B} {f} {g} ≡ id
happly-funext-to-id = funext (pr₁ (pr₂ (pr₂ happly-isEquiv)))





-- Dependent funext

happlyD : {i j : Level} {A : Type i} {B : A → Type j} {f g : (x : A) → B x}
          → f ≡ g → f ~ g
happlyD refl x₁ = refl

postulate
  happlyD-isEquiv : {i j : Level} {A : Type i} {B : A → Type j} {f g : (x : A) → B x}
                    → isEquiv (happlyD {i} {j} {A} {B} {f} {g})


abstract
  funextD : {i j : Level} {A : Type i} {B : A → Type j} {f g : (x : A) → B x}
            → (f ~ g) → f ≡ g
  funextD = pr₁ happlyD-isEquiv

funextD-equiv : {i j : Level} {A : Type i} {B : A → Type j} {f g : (x : A) → B x}
                → (f ≡ g) ≃ (f ~ g)
funextD-equiv = happlyD , happlyD-isEquiv


{- Univalence -}

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

{- Propositional resizing -}

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
