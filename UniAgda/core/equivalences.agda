{-# OPTIONS --without-K  #-}
module UniAgda.core.equivalences where

open import UniAgda.core.homotopy public
open import UniAgda.core.contr-prop-set public

-- Quasi-inverses
qinv : {i j : Level} {A : Type i} {B : Type j}
       (f : A → B)
       → Type (i ⊔ j)
qinv {_} {_} {A} {B} f = Σ[ g ∈ (B → A)] (((f o g) ~ id) × ((g o f) ~ id))

qequiv : {i j : Level}
         (A : Type i) (B : Type j)
         → Type (i ⊔ j)
qequiv A B = Σ[ f ∈ (A → B) ] (qinv f)
_q≃_ = qequiv
infix 6 _q≃_

-- qinv is equivalence relation
qinv-id : {i : Level} {A : Type i}
          → qinv (id {_} {A})
qinv-id = id , ((λ x → refl) , (λ x → refl))

qequiv-refl : {i : Level} {A : Type i}
              → A q≃ A
qequiv-refl = id , qinv-id
qrefl = qequiv-refl

qinv-inv : {i j : Level} {A : Type i} {B : Type j} {f : A → B}
           (F : qinv f)
           → qinv (pr₁ F)
qinv-inv {_} {_} {A} {B} {f} F = f , ((pr₂ (pr₂ F)) , (pr₁ (pr₂ F)))
_^q = qinv-inv

qequiv-sym : {i j : Level} {A : Type i} {B : Type j}
              → A q≃ B
              → B q≃ A
qequiv-sym X = (pr₁ (pr₂ X)) , (qinv-inv (pr₂ X))


qinv-comp : {i₁ i₂ i₃ : Level} {A : Type i₁} {B : Type i₂} {C : Type i₃} {f : A → B} {g : B → C}
             (F : qinv f) → (G : qinv g)
             → qinv (g o f)
qinv-comp {_} {_} {_} {A} {B} {C} {f} {g} F G = let f' : B → A
                                                    f' = pr₁ F
                                                    g' : C → B
                                                    g' = pr₁ G
                                                in (f' o g') , ((λ x → (ap g ((pr₁ (pr₂ F)) (pr₁ G x))) ∘ pr₁ (pr₂ G) x) , λ x → ap f' (pr₂ (pr₂ G) (f x)) ∘ pr₂ (pr₂ F) x)

qequiv-trans : {i₁ i₂ i₃ : Level} {A : Type i₁} {B : Type i₂} {C : Type i₃}
               → A q≃ B → B q≃ C
               → A q≃ C
qequiv-trans X Y = (pr₁ Y o pr₁ X) , qinv-comp (pr₂ X) (pr₂ Y)

_qo_ = qequiv-trans

-- Half adjoint equivalences
ishae : {i j : Level} {A : Type i} {B : Type j}
        (f : A → B)
        → Type (i ⊔ j)
ishae {_} {_} {A} {B} f = Σ[ g ∈ (B → A) ] (Σ[ η ∈ (g o f ~ id) ] (Σ[ ε ∈ (f o g ~ id) ] ((x : A) → ap f (η x) ≡ ε (f x))))

linv : {i j : Level} {A : Type i} {B : Type j}
       (f : A → B)
       → Type (i ⊔ j)
linv {_} {_} {A} {B} f = Σ[ g ∈ (B → A) ] (g o f ~ id)

rinv : {i j : Level} {A : Type i} {B : Type j}
       (f : A → B)
       → Type (i ⊔ j)
rinv {_} {_} {A} {B} f = Σ[ g ∈ (B → A) ] (f o g ~ id)

lcoh : {i j : Level} {A : Type i} {B : Type j}
       (f : A → B) (X : linv f)
       → Type (i ⊔ j)
lcoh {i} {j} {A} {B} f (g , η) = Σ[ ε ∈ (f o g ~ id) ] ((y : B) → ap g (ε y) ≡ η (g y))

rcoh : {i j : Level} {A : Type i} {B : Type j}
       (f : A → B) (Y : rinv f)
       → Type (i ⊔ j)
rcoh {i} {j} {A} {B} f (g , ε) = Σ[ η ∈ (g o f ~ id) ] ((x : A) → ap f (η x) ≡ ε (f x))


-- Bi-inveritble maps
isBiinv : {i j : Level} {A : Type i} {B : Type j}
        (f : A → B)
        → Type (i ⊔ j)
isBiinv {_} {_} {A} {B} f = linv f × rinv f

biequiv : {i j : Level}
          (A : Type i) (B : Type j)
          → Type (i ⊔ j)
biequiv A B = Σ[ f ∈ (A → B) ] (isBiinv f)
_bi≃_ = biequiv
infix 6 _bi≃_

-- Equivalences

isEquiv : {i j : Level} {A : Type i} {B : Type j}
          (f : A → B)
          → Type (i ⊔ j)
isEquiv f = ishae f

equiv : {i j : Level}
        (A : Type i) (B : Type j)
        → Type (i ⊔ j)
equiv A B = Σ[ f ∈ (A → B) ] (isEquiv f)
_≃_ = equiv
infix 31 _≃_

e-ap : {i j : Level} {A : Type i} {B : Type j}
      → A ≃ B → A
      → B
e-ap X a = pr₁ X a


-- Contractible fibres
fibre : {i j : Level} {A : Type i} {B : Type j}
        (f : A → B) (y : B)
        → Type (i ⊔ j)
fibre {_} {_} {A} f y = Σ[ x ∈ A ] (f x ≡ y)
fib = fibre


isContrmap : {i j : Level} {A : Type i} {B : Type j}
           (f : A → B) → Type (i ⊔ j)
isContrmap {_} {_} {A} {B} f = (y : B) → isContr (fib f y)



-- qinv and isBiinv relations
qinv-to-isBiinv : {i j : Level} {A : Type i} {B : Type j} {f : A → B}
                → qinv f
                → isBiinv f
qinv-to-isBiinv x = ((pr₁ x) , pr₂ (pr₂ x)) , ((pr₁ x) , (pr₁ (pr₂ x)))

isBiinv-to-qinv : {i j : Level} {A : Type i} {B : Type j} {f : A → B}
                → isBiinv f
                → qinv f
isBiinv-to-qinv {_} {_} {A} {B} {f} x = let h : B → A
                                            h = pr₁ (pr₁ x)
                                            g : B → A
                                            g = pr₁ (pr₂ x)
                                            α : (f o g) ~ id
                                            α = pr₂ (pr₂ x)
                                            β : (h o f) ~ id
                                            β = pr₂ (pr₁ x)
                                            γ = λ (b : B) → (β (g b) ^) ∘ (ap h (α b))
                                        in g , (α , λ x₁ → γ (f x₁) ∘ (β x₁))

qequiv-to-biequiv : {i j : Level} {A : Type i} {B : Type j}
                    → A q≃ B
                    → A bi≃ B
qequiv-to-biequiv X = (pr₁ X) , (qinv-to-isBiinv (pr₂ X))

biequiv-to-qequiv : {i j : Level} {A : Type i} {B : Type j}
                    → A bi≃ B
                    → A q≃ B
biequiv-to-qequiv X = pr₁ X , isBiinv-to-qinv (pr₂ X)

-- isBiinv is equivalence relation
isBiinv-id : {i : Level} {A : Type i}
            → isBiinv (id {_} {A})
isBiinv-id = qinv-to-isBiinv qinv-id

biequiv-refl : {i : Level} {A : Type i}
               → A bi≃ A
biequiv-refl = qequiv-to-biequiv qequiv-refl


biequiv-sym : {i j : Level} {A : Type i} {B : Type j}
              → A bi≃ B
              → B bi≃ A
biequiv-sym X = qequiv-to-biequiv (qequiv-sym (biequiv-to-qequiv X))
_^ᵇ = biequiv-sym

isBiinv-inv : {i j : Level} {A : Type i} {B : Type j} {f : A → B}
           (F : isBiinv f)
           → Σ[ g ∈ (B → A) ] (isBiinv g)
isBiinv-inv {_} {_} {A} {B} {f} F = biequiv-sym (f , F)


isBiinv-comp : {i₁ i₂ i₃ : Level} {A : Type i₁} {B : Type i₂} {C : Type i₃} {f : A → B} {g : B → C}
             (F : isBiinv f) → (G : isBiinv g)
             → isBiinv (g o f)
isBiinv-comp F G = qinv-to-isBiinv (qinv-comp (isBiinv-to-qinv F) (isBiinv-to-qinv G))

biequiv-trans : {i₁ i₂ i₃ : Level} {A : Type i₁} {B : Type i₂} {C : Type i₃}
                → A bi≃ B → B bi≃ C
                → A bi≃ C
biequiv-trans X Y = qequiv-to-biequiv (qequiv-trans (biequiv-to-qequiv X) (biequiv-to-qequiv Y))


-- qinv and ishae relations
ishae-to-qinv : {i j : Level} {A : Type i} {B : Type j} {f : A → B}
                → ishae f
                → qinv f
ishae-to-qinv F = (pr₁ F) , ((pr₁ (pr₂ (pr₂ F))) , (pr₁ (pr₂ F)))
isEquiv-to-qinv = ishae-to-qinv


qinv-to-ishae : {i j : Level} {A : Type i} {B : Type j} {f : A → B}
                → qinv f
                → ishae f
qinv-to-ishae {_} {_} {A} {B} {f} F = let g : B → A
                                          g = pr₁ F
                                          η : g o f ~ id
                                          η = pr₂ (pr₂ F)
                                          ε : f o g ~ id
                                          ε = pr₁ (pr₂ F)
                                      in g , (η , ((λ b → ((ε (f (g (b))) ^) ∘ (ap f (η (g b)))) ∘ (ε b) ) , (λ a →  (ap (λ p → p ∘ (ap f (η a))) (p^p (ε (f (g (f a)))))) ^ ∘ ( ass-l (ε (f (g (f a))) ^) (ε (f (g (f a)))) (ap f (η a)) ∘ ( ((ap (λ p → ((ε (f (g (f a)))) ^) ∘ p) ((homotopy-natural (λ x → ε (f x)) (η a)) ^)) ^) ∘ ( ap (λ p → ((ε (f (g (f a))) ^) ∘ (p ∘ (ε (f a))))) ((ap-gf f (g o f) (η a)) ∘ ap (λ α → (ap f α)) (cor2-4-4 (g o f) η a ^)) ∘ (ass-r (ε (f (g (f a))) ^) (ap f (η (g (f a)))) (ε (f (a))))))))))

qequiv-to-hae : {i j : Level} {A : Type i} {B : Type j}
                → A q≃ B
                → A ≃ B
qequiv-to-hae X = (pr₁ X) , (qinv-to-ishae (pr₂ X))

hae-to-qequiv : {i j : Level} {A : Type i} {B : Type j}
                → A ≃ B
                → A q≃ B
hae-to-qequiv X = (pr₁ X) , (ishae-to-qinv (pr₂ X))

isequiv-adjointify = qinv-to-ishae

equiv-adjointify = qequiv-to-hae

-- ishae is equivalence relation
equiv-refl : {i : Level} {A : Type i}
           → A ≃ A
equiv-refl = equiv-adjointify qequiv-refl
erefl = equiv-refl

ishae-id : {i : Level} {A : Type i}
           → ishae (id {_} {A})
ishae-id = pr₂ equiv-refl

equiv-sym : {i j : Level} {A : Type i} {B : Type j}
            → A ≃ B
            → B ≃ A
equiv-sym X = equiv-adjointify (qequiv-sym (hae-to-qequiv X))
_^ᵉ = equiv-sym

ishae-inv : {i j : Level} {A : Type i} {B : Type j} {f : A → B}
            → ishae f
            → Σ[ g ∈ (B → A) ] (ishae g)
ishae-inv {_} {_} {A} {B} {f} X = equiv-sym (f , X)

equiv-trans : {i₁ i₂ i₃ : Level} {A : Type i₁} {B : Type i₂} {C : Type i₃}
              → A ≃ B → B ≃ C
              → A ≃ C
equiv-trans F G = equiv-adjointify (qequiv-trans (hae-to-qequiv F) (hae-to-qequiv G))
_oₑ_ = equiv-trans


ishae-comp : {i₁ i₂ i₃ : Level} {A : Type i₁} {B : Type i₂} {C : Type i₃} {f : A → B} {g : B → C}
             (F : ishae f) (G : ishae g)
             → Σ[ h ∈ (A → C) ] (ishae h)
ishae-comp {_} {_} {_} {_} {_} {_} {f} {g} F G = equiv-trans (f , F) (g , G)

-- Contractible fibres

isContrmap-to-isEquiv : {i j : Level} {A : Type i} {B : Type j} {f : A → B}
                   → isContrmap f
                   → ishae f
isContrmap-to-isEquiv {_} {_} {A} {B} {f} P = let g = (λ y → pr₁ (pr₁ (P y)))
                                                  ε = (λ y → pr₂ (pr₁ (P y)))
                                                  τ = (λ x → (pr₂ (P (f x)) (g(f(x)) , ε (f x))) ^ ∘ (pr₂ (P (f x)) (x , refl)))
                                              in isequiv-adjointify (g , ε ,  λ x → ap pr₁ (τ x))

-- isEquiv-to-isContrmap - proven in prop-set-properties


inv-isContrmap : {i j : Level} {A : Type i} {B : Type j} {f : A → B}
                 → isContrmap f → B → A
inv-isContrmap X b = pr₁ (pr₁ (X b))

issect-isContrmap : {i j : Level} {A : Type i} {B : Type j} {f : A → B}
                    (X : isContrmap f)
                    → (f o inv-isContrmap X) ~ id
issect-isContrmap X y = pr₂ (pr₁ (X y))

const : {i j : Level}
        (A : Type i) (B : Type j) (b : B)
        → A → B
const A B b x = b

abstract
  centre : {i : Level} {A : Type i}
         → isContr A
         → A
  centre (c , is-contr-A) = c

  contraction : {i : Level} {A : Type i}
                (X : isContr A)
                → const A A (centre X) ~ id
  contraction (c , C) x =  C c ^ ∘ C x


isretr-isContrmap : {i j : Level} {A : Type i} {B : Type j} {f : A → B}
                    (X : isContrmap f)
                    → (inv-isContrmap X o f) ~ id
isretr-isContrmap {_} {_} {A} {B} {f} X x = ap ( pr₁ {B = λ z → f z ≡ f x}) (
  (contraction
    (X (f x))
      (inv-isContrmap X (f x) , issect-isContrmap X (f x))) ^ ∘
      (contraction (X (f x)) (x , refl)) )


-- This is used to prove equalities in a type, given that type is equivalent to another on.

equiv-types-eq : ∀ {i} {A B : Type i}
        (x y : B) (F : A ≃ B)
        → pr₁ (pr₂ F) x ≡ pr₁ (pr₂ F) y → x ≡ y
equiv-types-eq x y (f , g , η , ε , τ) p = ε x ^ ∘ (ap f p) ∘ ε y
