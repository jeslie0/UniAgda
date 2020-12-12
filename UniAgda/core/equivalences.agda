{-# OPTIONS --without-K #-}
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
             (G : qinv g) → (F : qinv f)
             → qinv (g o f)
qinv-comp {_} {_} {_} {A} {B} {C} {f} {g} G F = let f' : B → A
                                                    f' = pr₁ F
                                                    g' : C → B
                                                    g' = pr₁ G
                                                in (f' o g') , ((λ x → (ap g ((pr₁ (pr₂ F)) (pr₁ G x))) ∘ pr₁ (pr₂ G) x) , λ x → ap f' (pr₂ (pr₂ G) (f x)) ∘ pr₂ (pr₂ F) x)
_qo_ = qinv-comp

qequiv-trans : {i₁ i₂ i₃ : Level} {A : Type i₁} {B : Type i₂} {C : Type i₃}
               → A q≃ B → B q≃ C
               → A q≃ C
qequiv-trans X Y = (pr₁ Y o pr₁ X) , qinv-comp (pr₂ Y) (pr₂ X)


-- Half adjoint equivalences
ishae : {i j : Level} {A : Type i} {B : Type j}
        (f : A → B)
        → Type (i ⊔ j)
ishae {_} {_} {A} {B} f = Σ[ g ∈ (B → A) ] (Σ[ η ∈ (g o f ~ id) ] (Σ[ ε ∈ (f o g ~ id) ] ((x : A) → ap f (η x) ≡ ε (f x))))

-- Bi-inveritble maps
linv : {i j : Level} {A : Type i} {B : Type j}
       (f : A → B)
       → Type (i ⊔ j)
linv {_} {_} {A} {B} f = Σ[ g ∈ (B → A) ] (g o f ~ id)

rinv : {i j : Level} {A : Type i} {B : Type j}
       (f : A → B)
       → Type (i ⊔ j)
rinv {_} {_} {A} {B} f = Σ[ g ∈ (B → A) ] (f o g ~ id)

biinv : {i j : Level} {A : Type i} {B : Type j}
        (f : A → B)
        → Type (i ⊔ j)
biinv {_} {_} {A} {B} f = linv f × rinv f

biequiv : {i j : Level}
          (A : Type i) (B : Type j)
          → Type (i ⊔ j)
biequiv A B = Σ[ f ∈ (A → B) ] (biinv f)
_bi≃_ = biequiv
infix 6 _bi≃_

-- Equivalences

isequiv : {i j : Level} {A : Type i} {B : Type j}
          (f : A → B)
          → Type (i ⊔ j)
isequiv f = ishae f

equiv : {i j : Level}
        (A : Type i) (B : Type j)
        → Type (i ⊔ j)
equiv A B = Σ[ f ∈ (A → B) ] (isequiv f)
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



-- qinv and biinv relations
qinv-to-biinv : {i j : Level} {A : Type i} {B : Type j} {f : A → B}
                → qinv f
                → biinv f
qinv-to-biinv x = ((pr₁ x) , pr₂ (pr₂ x)) , ((pr₁ x) , (pr₁ (pr₂ x)))

biinv-to-qinv : {i j : Level} {A : Type i} {B : Type j} {f : A → B}
                → biinv f
                → qinv f
biinv-to-qinv {_} {_} {A} {B} {f} x = let h : B → A
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
qequiv-to-biequiv X = (pr₁ X) , (qinv-to-biinv (pr₂ X))

biequiv-to-qequiv : {i j : Level} {A : Type i} {B : Type j}
                    → A bi≃ B
                    → A q≃ B
biequiv-to-qequiv X = pr₁ X , biinv-to-qinv (pr₂ X)

-- biinv is equivalence relation
biinv-id : {i : Level} {A : Type i}
            → biinv (id {_} {A})
biinv-id = qinv-to-biinv qinv-id

biequiv-refl : {i : Level} {A : Type i}
               → A bi≃ A
biequiv-refl = qequiv-to-biequiv qequiv-refl


biequiv-sym : {i j : Level} {A : Type i} {B : Type j}
              → A bi≃ B
              → B bi≃ A
biequiv-sym X = qequiv-to-biequiv (qequiv-sym (biequiv-to-qequiv X))


biinv-inv : {i j : Level} {A : Type i} {B : Type j} {f : A → B}
           (F : biinv f)
           → Σ[ g ∈ (B → A) ] (biinv g)
biinv-inv {_} {_} {A} {B} {f} F = biequiv-sym (f , F)
_^b = biinv-inv


biinv-comp : {i₁ i₂ i₃ : Level} {A : Type i₁} {B : Type i₂} {C : Type i₃} {f : A → B} {g : B → C}
             (G : biinv g) → (F : biinv f)
             → biinv (g o f)
biinv-comp G F = qinv-to-biinv (qinv-comp (biinv-to-qinv G) (biinv-to-qinv F))

biequiv-trans : {i₁ i₂ i₃ : Level} {A : Type i₁} {B : Type i₂} {C : Type i₃}
                → A bi≃ B → B bi≃ C
                → A bi≃ C
biequiv-trans X Y = qequiv-to-biequiv (qequiv-trans (biequiv-to-qequiv X) (biequiv-to-qequiv Y))


-- qinv and ishae relations
ishae-to-qinv : {i j : Level} {A : Type i} {B : Type j} {f : A → B}
                → ishae f
                → qinv f
ishae-to-qinv F = (pr₁ F) , ((pr₁ (pr₂ (pr₂ F))) , (pr₁ (pr₂ F)))

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
              → B ≃ C → A ≃ B
              → A ≃ C
equiv-trans G F = equiv-adjointify (qequiv-trans (hae-to-qequiv F) (hae-to-qequiv G))
_oₑ_ = equiv-trans


ishae-comp : {i₁ i₂ i₃ : Level} {A : Type i₁} {B : Type i₂} {C : Type i₃} {f : A → B} {g : B → C}
             (F : ishae f) (G : ishae g)
             → Σ[ h ∈ (A → C) ] (ishae h)
ishae-comp {_} {_} {_} {_} {_} {_} {f} {g} F G = equiv-trans (g , G) (f , F)

-- Contractible fibres

isContrmap-to-isequiv : {i j : Level} {A : Type i} {B : Type j} {f : A → B}
                   → isContrmap f
                   → ishae f
isContrmap-to-isequiv {_} {_} {A} {B} {f} P = let g = (λ y → pr₁ (pr₁ (P y)))
                                                  ε = (λ y → pr₂ (pr₁ (P y)))
                                                  τ = (λ x → (pr₂ (P (f x)) (g(f(x)) , ε (f x))) ^ ∘ (pr₂ (P (f x)) (x , refl)))
                                              in isequiv-adjointify (g , ε ,  λ x → ap pr₁ (τ x))

-- isequiv-to-isContr : {i : Level} {A : Type i} {B : Type i} {f : A → B}
--                      → isequiv f
--                      → fisContr f
-- isequiv-to-isContr {_} {A} {B} {f} F y = (pr₁ F y , pr₁ (pr₃ F) y) , λ { (a , b) → path-equiv-sigma (pr₁ F y , pr₁ (pr₃ F) y) (a , b) ((ap (pr₁ F) (b ^) ∘ pr₁ (pr₂ F) a ) , {!!})}

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

-- isequiv-to-isContrmap : {i j : Level} {A : Type i} {B : Type j} {f : A → B}
--                         → isequiv f
--                         → isContrmap f
-- isequiv-to-isContrmap X y = ((pr₁ X y) , (pr₁ (pr₃ X) y)) , (λ { (a , b) → path-equiv-sigma _ _
--                             ((ap (pr₁ X )b ^ ∘ pr₁ (pr₂ X) a) , {!thm2-11-3!})})
