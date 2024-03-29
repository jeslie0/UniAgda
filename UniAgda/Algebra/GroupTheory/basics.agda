{-# OPTIONS --without-K --no-import-sorts #-}
module UniAgda.Algebra.GroupTheory.basics where

open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Functions
open import UniAgda.Core.Types.Identity
open import UniAgda.Core.Types.Sigma
open import UniAgda.Core.Types.Unit

open import UniAgda.Core.Homotopy
open import UniAgda.Core.Axioms
open import UniAgda.Core.Equivalences

open import UniAgda.Core.PathSpaces.Sigma
open import UniAgda.Core.SetsAndLogic.ContrPropSet1Type
open import UniAgda.Core.SetsAndLogic.Sets


-- * Group definition

record Group (i : Level) : Type (lsuc i) where
  eta-equality
  field
    carrier : Type i
    op : carrier → carrier → carrier
    _^ᵍ : carrier → carrier
    e : carrier

    carrier-set : isSet carrier
    gp-assoc : (a b c : carrier) → op (op a b) c ≡ op a (op b c)
    gp-lId : (a : carrier) → op e a ≡ a
    gp-rId : (a : carrier) → op a e ≡ a
    gp-lInv : (a : carrier) → op (a ^ᵍ) (a) ≡ e
    gp-rInv : (a : carrier) → op a (a ^ᵍ) ≡ e

  _og_ : carrier → carrier → carrier
  _og_ = op



  {- The identity is unique -}
  e-unique : (X : Σ[ e' ∈ carrier ] (
             ((a : carrier) → op e' a ≡ a) × (
             ((a : carrier) → op a e' ≡ a) × (
             ((a : carrier) → op (a ^ᵍ) (a) ≡ e) × (
             ((a : carrier) → op (a ^ᵍ) (a) ≡ e))))))
             → pr₁ X ≡ e
  e-unique (e' , lId , rId , linv , rinv) =
    gp-lId e' ^ ∘ rId e

  {- The inverse of an element is unique -}
  inv-unique : (a : carrier) → (X : Σ[ b ∈ carrier ] (
               (op b a ≡ e) ×
               (op a b ≡ e)))
               → pr₁ X ≡ (a ^ᵍ)
  inv-unique a (b , p , q) =
    gp-lId b ^ ∘
    transport (λ P → op P b ≡ (a ^ᵍ)) (gp-lInv a)
      (gp-assoc (a ^ᵍ) a b ∘
      transport (λ P → op (a ^ᵍ) P ≡ (a ^ᵍ)) (q ^)
        (gp-rId (a ^ᵍ)) )

  {- inverse is an involution -}
  inv-involution : (a : carrier)
                   → (a ^ᵍ ) ^ᵍ ≡ a
  inv-involution a =
    inv-unique
      (a ^ᵍ)
      (a ,
      ((gp-rInv a) ,
       (gp-lInv a))) ^

  inv-of-prod : (a b : carrier)
                → (a og b) ^ᵍ ≡ (b ^ᵍ) og (a ^ᵍ)
  inv-of-prod a b =
    inv-unique
      (a og b)
      ((b ^ᵍ) og (a ^ᵍ) ,
      gp-assoc (b ^ᵍ) (a ^ᵍ) (a og b) ∘
        ap (λ z → op (b ^ᵍ) z) (gp-assoc (a ^ᵍ) a b ^) ∘
        ap (λ z → op (b ^ᵍ) (op z b)) (gp-lInv a) ∘
        ap (λ z → op (b ^ᵍ) z) (gp-lId b) ∘
        gp-lInv b ,
      gp-assoc a b ((b ^ᵍ) og (a ^ᵍ)) ∘
        ap (λ z → op a z) (gp-assoc b (b ^ᵍ) (a ^ᵍ) ^) ∘
        ap (λ z → op a (op z (a ^ᵍ))) (gp-rInv b) ∘
        ap (λ z → op a z) (gp-lId (a ^ᵍ)) ∘
        gp-rInv a) ^

  {- left and right cancellation laws -}
  gp-lCancel : (a b c : carrier)
               → a og b ≡ a og c
               → b ≡ c
  gp-lCancel a b c p =
    gp-lId b ^ ∘
    (ap (λ z → op z b) (gp-lInv a) ^ ∘
    (gp-assoc (a ^ᵍ) a b ∘
    ap (λ z → op (a ^ᵍ) z) p ∘
    gp-assoc (a ^ᵍ) a c ^) ∘
    ap (λ z → op z c) (gp-lInv a)) ∘
    gp-lId c

  gp-rCancel : (a b c : carrier)
               → b og a ≡ c og a
               → b ≡ c
  gp-rCancel a b c p =
    gp-rId b ^ ∘
    (ap (λ z → b og z) (gp-rInv a)) ^ ∘
    gp-assoc b a (a ^ᵍ) ^ ∘
    ap (λ z → op z (a ^ᵍ)) p ∘
    gp-assoc c a (a ^ᵍ) ∘
    ap (λ z → op c z) (gp-rInv a) ∘
    gp-rId c


-- ** Sigma definition

Group-sig : (i : Level) → Type (lsuc i)
Group-sig i =
  Σ[ carrier ∈ (Type i) ](
    Σ[ op ∈ (carrier → carrier → carrier) ] (
      Σ[ inv ∈ (carrier → carrier) ] (
        Σ[ e ∈ carrier ] (
          Σ[ carrier-set ∈ (isSet carrier) ] (
           Σ[ gp-assoc ∈ ((a b c : carrier) → op (op a b) c ≡ op a (op b c)) ] (
             Σ[ gp-lId ∈ ((a : carrier) → op e a ≡ a) ] (
               Σ[ gp-rId ∈ ((a : carrier) → op a e ≡ a) ] (
                Σ[ gp-lInv ∈ ((a : carrier) → op (inv a) a ≡ e) ] (
                   (a : carrier) → op a (inv a) ≡ e)))))))))
    
Group-sig→rec : ∀ {i}
                → Group-sig i → Group i
Group.carrier (Group-sig→rec G) = pr₁ G
Group.op (Group-sig→rec G) = pr₁ (pr₂ G)
Group-sig→rec G Group.^ᵍ = pr₁ (pr₂ (pr₂ G))
Group.e (Group-sig→rec G) = pr₁ (pr₂ (pr₂ (pr₂ G)))
Group.carrier-set (Group-sig→rec G) = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ G))))
Group.gp-assoc (Group-sig→rec G) = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ G)))))
Group.gp-lId (Group-sig→rec G) = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ G))))))
Group.gp-rId (Group-sig→rec G) = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ G)))))))
Group.gp-lInv (Group-sig→rec G) = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ G))))))))
Group.gp-rInv (Group-sig→rec G) = pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₂ G))))))))



Group-rec→sig : ∀ {i}
                → Group i → Group-sig i
Group-rec→sig G =
  let module G = Group G in
  G.carrier ,
  G.op ,
  G._^ᵍ ,
  G.e ,
  G.carrier-set ,
  G.gp-assoc ,
  G.gp-lId ,
  G.gp-rId ,
  G.gp-lInv ,
  G.gp-rInv

Group-rec→sig→rec : ∀ {i}
                    (G : Group i)
                    → (Group-sig→rec o Group-rec→sig) G ≡ G
Group-rec→sig→rec G = refl

Group-sig→rec→sig : ∀ {i}
                    (G : Group-sig i)
                    → (Group-rec→sig o Group-sig→rec) G ≡ G
Group-sig→rec→sig G =
  path-equiv-sigma (refl ,
    path-equiv-sigma (refl ,
      (path-equiv-sigma (refl ,
        (path-equiv-sigma (refl ,
          (path-equiv-sigma (refl ,
            (path-equiv-sigma (refl ,
              (path-equiv-sigma (refl ,
                (path-equiv-sigma (refl ,
                  (path-equiv-sigma (refl ,
                    refl))))))))))))))))

Group-sig-Equiv : ∀ {i}
                  → Group-sig i ≃ Group i
Group-sig-Equiv = equiv-adjointify
  (Group-sig→rec ,
  Group-rec→sig ,
  Group-rec→sig→rec ,
  Group-sig→rec→sig)



-- * Group homomorphism definition

record Group-hom {i j : Level} (G : Group i) (H : Group j) : Type (i ⊔ j) where
  eta-equality
  module G = Group G
  module H = Group H
  field
    g-func : G.carrier → H.carrier
    g-linear : (g g' : G.carrier) → g-func (g G.og g') ≡ g-func g H.og (g-func g')

-- ** Group homomorphism sig version

Group-hom-sig : ∀ {i j}
                (G : Group i) (H : Group j)
                → Type (i ⊔ j)
Group-hom-sig G H =
  let module G = Group G in
  let module H = Group H in
  Σ[ g-func ∈ (G.carrier → H.carrier) ] ((g g' : G.carrier) → g-func (g G.og g') ≡ g-func g H.og (g-func g'))

Group-hom-sig→rec : ∀ {i j} {G : Group i} {H : Group j}
                    → Group-hom-sig G H → Group-hom G H
Group-hom.g-func (Group-hom-sig→rec f) = pr₁ f
Group-hom.g-linear (Group-hom-sig→rec f) = pr₂ f

Group-hom-rec→sig : ∀ {i j} {G : Group i} {H : Group j}
                    → Group-hom G H → Group-hom-sig G H
Group-hom-rec→sig f =
  let module f = Group-hom f in
  f.g-func ,
  f.g-linear

Group-hom-rec→sig→rec : ∀ {i j} {G : Group i} {H : Group j}
                        (f : Group-hom G H)
                        → (Group-hom-sig→rec o Group-hom-rec→sig) f ≡ f
Group-hom-rec→sig→rec f = refl

Group-hom-sig→rec→sig : ∀ {i j} {G : Group i} {H : Group j}
                        (f : Group-hom-sig G H)
                        → (Group-hom-rec→sig o Group-hom-sig→rec {i} {j} {G} {H}) f ≡ f
Group-hom-sig→rec→sig f =
  path-equiv-sigma (refl , refl)

Group-hom-sig-Equiv : ∀ {i j} {G : Group i} {H : Group j}
                      → Group-hom-sig G H ≃ Group-hom G H
Group-hom-sig-Equiv {i} {j} {G} {H} = equiv-adjointify
  (Group-hom-sig→rec ,
  Group-hom-rec→sig ,
  Group-hom-rec→sig→rec ,
  Group-hom-sig→rec→sig {i} {j} {G} {H})

-- ** Equality of Group homomorphisms
-- Two group homomorphisms are equal exactly when their functions are
-- equal.

Group-hom-eq : ∀ {i j} {G : Group i} {H : Group j} {f g : Group-hom G H}
               → Group-hom.g-func f ≡ Group-hom.g-func g → f ≡ g
Group-hom-eq {H = H} p =
  let module H = Group H in
  equiv-types-eq
    Group-hom-sig-Equiv
    (path-equiv-sigma (p ,
      funextD λ a →
      funextD λ b →
        H.carrier-set _ _ _ _))


-- This shows that we have a set of group homomorphisms between two
-- groups.

Group-hom-is-set : ∀ {i j} {G : Group i} {H : Group j}
                   → isSet (Group-hom G H)
Group-hom-is-set {G = G} {H = H} =
  equiv-with-set
    Group-hom-sig-Equiv
    (prop-fibres-totalspace-set
      (fibs-are-sets-PI-is-set λ x → Group.carrier-set H)
      λ a P Q →
        funextD λ x →
        funextD λ y →
          sets-have-prop-ids _ (Group.carrier-set H) _ _ _ _)

-- ** Categorical properties
-- Group homomorphisms can be composed.

ghom-comp : ∀ {i j k} {G : Group i} {H : Group j} {K : Group k}
             → Group-hom H K → Group-hom G H → Group-hom G K
Group-hom.g-func (ghom-comp g f) = Group-hom.g-func g o Group-hom.g-func f
Group-hom.g-linear (ghom-comp {G = G} {H = H} {K = K} g f) a b =
  let module G = Group G in
  let module H = Group H in
  let module K = Group K in
  let module g = Group-hom g in
  let module f = Group-hom f in
    ap (g.g-func) (f.g-linear a b) ∘
    g.g-linear (f.g-func a) (f.g-func b)


-- We have an identity group homomorphism for every group.

Idᵍ : ∀ {i} {G : Group i}
      → Group-hom G G
Group-hom.g-func Idᵍ = id
Group-hom.g-linear Idᵍ g g' = refl


-- Composition on the left and right with the identity doesn't change the morphism.

ghom-lId : ∀ {i j} {G : Group i} {H : Group j}
           (f : Group-hom G H)
           → ghom-comp f Idᵍ ≡ f
ghom-lId f = Group-hom-eq refl

ghom-rId : ∀ {i j} {G : Group i} {H : Group j}
             (f : Group-hom G H)
           → ghom-comp Idᵍ f ≡ f
ghom-rId f = Group-hom-eq refl


-- Finally, composition is associative.

ghom-assoc : ∀ {i₁ i₂ i₃ i₄} {G₁ : Group i₁} {G₂ : Group i₂} {G₃ : Group i₃} {G₄ : Group i₄}
             (f : Group-hom G₁ G₂) (g : Group-hom G₂ G₃) (h : Group-hom G₃ G₄)
             → ghom-comp h (ghom-comp g f) ≡ ghom-comp (ghom-comp h g) f
ghom-assoc f g h = Group-hom-eq refl

-- * Trivial Group
-- There is a trivial group that has exactly one element in it.

Group-trivial : Group lzero
Group.carrier Group-trivial = Unit
Group.op Group-trivial = λ _ _ → tt
Group-trivial Group.^ᵍ = λ _ → tt
Group.e Group-trivial = tt
Group.carrier-set Group-trivial = Unit-is-set
Group.gp-assoc Group-trivial = λ _ _ _ → refl
Group.gp-lId Group-trivial = λ { tt → refl }
Group.gp-rId Group-trivial = λ { tt → refl }
Group.gp-lInv Group-trivial = λ _ → refl
Group.gp-rInv Group-trivial = λ _ → refl
