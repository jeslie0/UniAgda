{-# OPTIONS --without-K --safe --no-import-sorts #-}
module UniAgda.Core.Equivalences where

open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Functions
open import UniAgda.Core.Types.Identity
open import UniAgda.Core.Types.Sigma

open import UniAgda.Core.Homotopy
open import UniAgda.Core.SetsAndLogic.ContrPropSet1Type
open import UniAgda.Core.PathAlgebra
-- * Quasi-inverses
-- ** Definition
-- A quasi-inverse is what we would call an isomorphism if we were
-- dealing with sets. It is a map with another map that is a left and
-- right inverse.

-- Definition2.4.6
qinv : ∀ {i j} {A : Type i} {B : Type j}
       (f : A → B)
       → Type (i ⊔ j)
qinv {A = A} {B = B} f = Σ[ g ∈ (B → A)] (((f o g) ~ id) × ((g o f) ~ id))

-- A quasi-equivalence between two types is then a map with a proof
-- that it is a quasi-inverse.
qequiv : ∀ {i j}
         (A : Type i) (B : Type j)
         → Type (i ⊔ j)
qequiv A B = Σ[ f ∈ (A → B) ] (qinv f)
_q≃_ = qequiv
infix 6 _q≃_

-- ** Equivalence Relation
 -- Quasi-equivalences are equivalence relations. Reflexivity is given
 -- by:
qinv-id : ∀ {i} {A : Type i}
          → qinv (id {A = A})
qinv-id = id , ((λ x → refl) , (λ x → refl))

qequiv-refl : ∀ {i} {A : Type i}
              → A q≃ A
qequiv-refl = id , qinv-id
qrefl = qequiv-refl

-- Symmetry:
qinv-inv : ∀{i j} {A : Type i} {B : Type j} {f : A → B}
           (F : qinv f)
           → qinv (pr₁ F)
qinv-inv {f = f} F = f , ((pr₂ (pr₂ F)) , (pr₁ (pr₂ F)))
_^q = qinv-inv

qequiv-sym : ∀ {i j} {A : Type i} {B : Type j}
              → A q≃ B
              → B q≃ A
qequiv-sym X = (pr₁ (pr₂ X)) , (qinv-inv (pr₂ X))

-- Transitivity:
qinv-comp : ∀ {i₁ i₂ i₃} {A : Type i₁} {B : Type i₂} {C : Type i₃} {f : A → B} {g : B → C}
            (F : qinv f) → (G : qinv g)
            → qinv (g o f)
qinv-comp {A = A} {B = B} {C = C} {f = f} {g = g} F G =
  let f' : B → A
      f' = pr₁ F
      g' : C → B
      g' = pr₁ G
  in
  (f' o g') ,
  ((λ x → (ap g ((pr₁ (pr₂ F)) (pr₁ G x))) ∘ pr₁ (pr₂ G) x) ,
    λ x → ap f' (pr₂ (pr₂ G) (f x)) ∘ pr₂ (pr₂ F) x)

qequiv-trans : ∀ {i₁ i₂ i₃} {A : Type i₁} {B : Type i₂} {C : Type i₃}
               → A q≃ B → B q≃ C
               → A q≃ C
qequiv-trans X Y = (pr₁ Y o pr₁ X) , qinv-comp (pr₂ X) (pr₂ Y)
_qo_ = qequiv-trans

-- * Half adjoint equivalences
-- ** Definition
-- Half adjoint equivalences will be our candidate for equivalences.

-- Definition4.2.1
isHae : ∀ {i j} {A : Type i} {B : Type j}
        (f : A → B)
        → Type (i ⊔ j)
isHae {A = A} {B = B} f = Σ[ g ∈ (B → A) ] (Σ[ η ∈ (g o f ~ id) ] (Σ[ ε ∈ (f o g ~ id) ] ((x : A) → ap f (η x) ≡ ε (f x))))

isEquiv = isHae

equiv : ∀ {i j}
        (A : Type i) (B : Type j)
        → Type (i ⊔ j)
equiv A B = Σ[ f ∈ (A → B) ] (isEquiv f)
_≃_ = equiv
infix 31 _≃_

-- We also define the following which will be useful when proving
-- relations between the different types of equivalence.

-- Definition4.2.7
linv : ∀ {i j} {A : Type i} {B : Type j}
       (f : A → B)
       → Type (i ⊔ j)
linv {_} {_} {A} {B} f = Σ[ g ∈ (B → A) ] (g o f ~ id)

rinv : ∀ {i j} {A : Type i} {B : Type j}
       (f : A → B)
       → Type (i ⊔ j)
rinv {_} {_} {A} {B} f = Σ[ g ∈ (B → A) ] (f o g ~ id)

-- Definition4.2.10
lcoh : ∀ {i j} {A : Type i} {B : Type j}
       (f : A → B) (X : linv f)
       → Type (i ⊔ j)
lcoh {i} {j} {A} {B} f (g , η) = Σ[ ε ∈ (f o g ~ id) ] ((y : B) → ap g (ε y) ≡ η (g y))

rcoh : ∀ {i j} {A : Type i} {B : Type j}
       (f : A → B) (Y : rinv f)
       → Type (i ⊔ j)
rcoh {i} {j} {A} {B} f (g , ε) = Σ[ η ∈ (g o f ~ id) ] ((x : A) → ap f (η x) ≡ ε (f x))

-- ** Relation to qinv

-- Theorem4.2.3
qinv-to-ishae : ∀ {i j} {A : Type i} {B : Type j} {f : A → B}
                → qinv f
                → isHae f
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

ishae-to-qinv : ∀ {i j} {A : Type i} {B : Type j} {f : A → B}
                → isHae f
                → qinv f
ishae-to-qinv F = (pr₁ F) , ((pr₁ (pr₂ (pr₂ F))) , (pr₁ (pr₂ F)))
isEquiv-to-qinv = ishae-to-qinv

hae-to-qequiv : {i j : Level} {A : Type i} {B : Type j}
                → A ≃ B
                → A q≃ B
hae-to-qequiv X = (pr₁ X) , (ishae-to-qinv (pr₂ X))

-- We will use these functions a lot when constructing equivalences,
-- so we give special names for referring to them.
isequiv-adjointify = qinv-to-ishae

equiv-adjointify = qequiv-to-hae

-- ** Equivalence relation
equiv-refl : {i : Level} {A : Type i}
           → A ≃ A
equiv-refl = equiv-adjointify qequiv-refl
erefl = equiv-refl

ishae-id : {i : Level} {A : Type i}
           → isHae (id {_} {A})
ishae-id = pr₂ equiv-refl

equiv-sym : {i j : Level} {A : Type i} {B : Type j}
            → A ≃ B
            → B ≃ A
equiv-sym X = equiv-adjointify (qequiv-sym (hae-to-qequiv X))
_^ᵉ = equiv-sym

ishae-inv : {i j : Level} {A : Type i} {B : Type j} {f : A → B}
            → isHae f
            → Σ[ g ∈ (B → A) ] (isHae g)
ishae-inv {_} {_} {A} {B} {f} X = equiv-sym (f , X)

equiv-trans : {i₁ i₂ i₃ : Level} {A : Type i₁} {B : Type i₂} {C : Type i₃}
              → A ≃ B → B ≃ C
              → A ≃ C
equiv-trans F G = equiv-adjointify (qequiv-trans (hae-to-qequiv F) (hae-to-qequiv G))
_oₑ_ = equiv-trans


ishae-comp : {i₁ i₂ i₃ : Level} {A : Type i₁} {B : Type i₂} {C : Type i₃} {f : A → B} {g : B → C}
             (F : isHae f) (G : isHae g)
             → Σ[ h ∈ (A → C) ] (isHae h)
ishae-comp {_} {_} {_} {_} {_} {_} {f} {g} F G = equiv-trans (f , F) (g , G)

-- * Bi-invertible maps
-- A bi-invertible map is one with both a left and right inverse.
-- Definition4.3.1
isBiinv : ∀ {i j} {A : Type i} {B : Type j}
        (f : A → B)
        → Type (i ⊔ j)
isBiinv f = linv f × rinv f


biequiv : ∀ {i j}
          (A : Type i) (B : Type j)
          → Type (i ⊔ j)
biequiv A B = Σ[ f ∈ (A → B) ] (isBiinv f)
_bi≃_ = biequiv
infix 6 _bi≃_

-- ** Relation to qinv
-- There are morphisms to and from the type of quasi inverses, which
-- extend to maps between the types of equivalences.

qinv-to-isBiinv : ∀ {i j} {A : Type i} {B : Type j} {f : A → B}
                → qinv f
                → isBiinv f
qinv-to-isBiinv x = ((pr₁ x) , pr₂ (pr₂ x)) , ((pr₁ x) , (pr₁ (pr₂ x)))

qequiv-to-biequiv : ∀ {i j} {A : Type i} {B : Type j}
                    → A q≃ B
                    → A bi≃ B
qequiv-to-biequiv X = (pr₁ X) , (qinv-to-isBiinv (pr₂ X))

isBiinv-to-qinv : ∀ {i j} {A : Type i} {B : Type j} {f : A → B}
                → isBiinv f
                → qinv f
isBiinv-to-qinv {_} {_} {A} {B} {f} x =
  let h : B → A
      h = pr₁ (pr₁ x)
      g : B → A
      g = pr₁ (pr₂ x)
      α : (f o g) ~ id
      α = pr₂ (pr₂ x)
      β : (h o f) ~ id
      β = pr₂ (pr₁ x)
      γ = λ (b : B) → (β (g b) ^) ∘ (ap h (α b))
  in
  g , (α , λ x₁ → γ (f x₁) ∘ (β x₁))


biequiv-to-qequiv : {i j : Level} {A : Type i} {B : Type j}
                    → A bi≃ B
                    → A q≃ B
biequiv-to-qequiv X = pr₁ X , isBiinv-to-qinv (pr₂ X)

-- ** Equivalence relation
-- isBiinv is an equivalence relation.

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

-- * Contractible fibres
-- ** Definition
-- We first need to define the fibre of a map and a point.

-- Definition4.2.4
fibre : ∀ {i j} {A : Type i} {B : Type j}
        (f : A → B) (y : B)
        → Type (i ⊔ j)
fibre {A = A} f y = Σ[ x ∈ A ] (f x ≡ y)
fib = fibre

-- We say that a map is contractible when all of its fibres are
-- contractible.
-- Definition4.4.1
isContrmap : {i j : Level} {A : Type i} {B : Type j}
           (f : A → B) → Type (i ⊔ j)
isContrmap {_} {_} {A} {B} f = (y : B) → isContr (fib f y)

-- ** Relation to isEquiv
isContrmap-to-isEquiv : {i j : Level} {A : Type i} {B : Type j} {f : A → B}
                   → isContrmap f
                   → isHae f
isContrmap-to-isEquiv {_} {_} {A} {B} {f} P = let g = (λ y → pr₁ (pr₁ (P y)))
                                                  ε = (λ y → pr₂ (pr₁ (P y)))
                                                  τ = (λ x → (pr₂ (P (f x)) (g(f(x)) , ε (f x))) ^ ∘ (pr₂ (P (f x)) (x , refl)))
                                              in isequiv-adjointify (g , ε ,  λ x → ap pr₁ (τ x))
-- More will be proven about this later, in another section. We need
-- results about contractible types to do this.

-- ** Other results
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


-- * Useful results
-- We can take an equivalence, a term of the first type then construct
-- a term of the second.
e-ap : ∀ {i j} {A : Type i} {B : Type j}
      → A ≃ B → A
      → B
e-ap X a = pr₁ X a

-- We want to be able to compare elements of equivalent types. This
-- doesn't really make sense on the nose though, so the following is
-- the closest that we have.
equiv-types-eq : ∀ {i j} {A : Type i} {B : Type j}
        {x y : B} (F : A ≃ B)
        → pr₁ (pr₂ F) x ≡ pr₁ (pr₂ F) y → x ≡ y
equiv-types-eq {x = x} {y = y} (f , g , η , ε , τ) p = ε x ^ ∘ (ap f p) ∘ ε y

-- Another useful result is that if we know two types are equivalent,
-- then \(\Pi\) and \(\Sigma\) types over one of the equivalent types
-- are logically equivalent, in the following sense:
equiv-base-Pi : ∀ {i j k} {A : Type i} {A' : Type j} {B : A → Type k}
      (F : A ≃ A')
      → ((x : A') → B o (pr₁ (pr₂ F)) $ x) → ((x : A) → B x)
equiv-base-Pi {B = B} (f , g , α , β , γ) Q a = transport B (α a) (Q (f a))

equiv-base-Sigma : ∀ {i j k} {A : Type i} {A' : Type j} {B : A → Type k}
                   (F : A ≃ A')
                   → (Σ[ x' ∈ A' ] (B o pr₁ (pr₂ F) $ x')) → (Σ[ x ∈ A ] B x)
equiv-base-Sigma (f , g , α , β , γ) (a' , b') = g a' , b'

-- Note that with univalence, these types are equivalent (I don't know
-- if we need univalence for this, but logical equivalence is
-- sufficient for our needs).

-- A result we expect is for the type of paths \(a = b\) to be
-- equivalent to the type of paths \(b = a\).
a=b≃b=a : ∀ {i} {A : Type i} {a b : A}
          → (a ≡ b) ≃ (b ≡ a)
a=b≃b=a = equiv-adjointify
  ((λ { refl → refl}) ,
  (λ { refl → refl}) ,
  (λ { refl → refl}) ,
  λ { refl → refl})
