{-# OPTIONS --without-K --no-import-sorts #-}
module UniAgda.Core.SetsAndLogic.Equivalences where

open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Functions
open import UniAgda.Core.Types.Identity
open import UniAgda.Core.Types.Sigma
open import UniAgda.Core.Types.Coproduct
open import UniAgda.Core.Types.W
open import UniAgda.Core.Types.Unit
open import UniAgda.Core.Types.Empty
open import UniAgda.Core.Types.Bool
open import UniAgda.Core.Types.Nat

open import UniAgda.Core.PathAlgebra
open import UniAgda.Core.Homotopy
open import UniAgda.Core.Equivalences
open import UniAgda.Core.SetsAndLogic.ContrPropSet1Type

open import UniAgda.Core.PathSpaces.Coproduct
open import UniAgda.Core.PathSpaces.Identity
open import UniAgda.Core.PathSpaces.Nat
open import UniAgda.Core.PathSpaces.Sigma
open import UniAgda.Core.PathSpaces.Unit

open import UniAgda.Core.Axioms
open import UniAgda.Core.SetsAndLogic.Props
open import UniAgda.Core.SetsAndLogic.Contractible

-- * Results


equiv-fibres-to-equiv-sigma : ∀ {i j } {A : Type i} {B : A → Type j} {C : A → Type j}
      → ((x : A) → (B x ≃ C x))
      → (Σ[ x ∈ A ] B x) ≃ (Σ[ x ∈ A ] C x)
equiv-fibres-to-equiv-sigma F = equiv-adjointify ((λ { (a , b) → a , pr₁ (F a) b}) ,
           (λ { (a , c) → a , (pr₁ (pr₂ (F a)) c)}) ,
           ((λ { (a , c) → path-equiv-sigma (refl , (pr₁ (pr₂ (pr₂ (pr₂ (F a)))) c ))}) ,
           λ { (a , b) → path-equiv-sigma (refl , (pr₁ (pr₂ (pr₂ (F a))) b))}))


p=p'-equiv-p'=p : ∀ {i} {A : Type i} {x y : A} {p p' : x ≡ y}
              → (p ≡ p') ≃ (p' ≡ p)
p=p'-equiv-p'=p {i} {A} {x} {y} {p} {p'} = equiv-adjointify ((λ α → α ^) ,
            (λ β → β ^) ,
            (λ { refl → refl}) ,
            λ { refl → refl})


lemma4-2-5 : ∀ {i j} {A : Type i} {B : Type j}
             {f : A → B} {y : B} (X Y : fib f y)
             → (X ≡ Y) ≃ (Σ[ γ ∈ (pr₁ X ≡ pr₁ Y) ] ((ap f γ) ∘ pr₂ Y ≡ pr₂ X))
lemma4-2-5 {i} {j} {A} {B} {f} {y} (x , p) (x' , p') = thm2-7-2 oₑ equiv-fibres-to-equiv-sigma (λ { refl → p=p'-equiv-p'=p})


lemma4-2-8i : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} {f : A → B}
              → qinv f
              → qinv (λ (g : C → A) → f o g)
lemma4-2-8i {i} {j} {k} {A} {B} {C} {f} (g , α , β ) = (λ h c → g (h c) ) , (λ h → funext λ c → α (h c)) , λ h → funext λ c → β (h c)


lemma4-2-8ii : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} {f : A → B}
               → qinv f
               → qinv (λ (g : B → C) → g o f)
lemma4-2-8ii {i} {j} {k} {A} {B} {C} {f} (g , α , β) = (λ h b → h (g b)) , (λ h → funext λ a → ap h (β a)) , λ h → funext λ a → ap h (α a)


Sigma-Pi-swap : ∀ {i j k} {A : Type i} {B : A → Type j} {C : (a : A) → B a → Type k}
                → ((x : A) → Σ[ y ∈ (B x) ] C x y) ≃ (Σ[ F ∈ ((x : A) → B x)] ((x : A) → C x (F x)))
Sigma-Pi-swap = equiv-adjointify ((λ F → (λ x → pr₁ (F x)) , λ x → pr₂ (F x)) ,
              ((λ { (F , P) x → (F x) , (P x)}) ,
              ((λ { (F , P) → path-equiv-sigma (refl , refl)}) ,
              λ F → funextD λ x → path-equiv-sigma (refl , refl))))

equiv-fibres-to-Pi : ∀ {i j k} {A  : Type i} {B : A → Type j} {C : A → Type k}
                     → ((x : A) → (B x ≃ C x))
                     → (((x : A) → B x) ≃ ((x : A) → C x))
equiv-fibres-to-Pi {i} {j} {k} {A} {B} {C} F = equiv-adjointify ((λ G x → pr₁ (F x) (G x)) ,
                   ((λ G x → pr₁ (pr₂ (F x)) (G x)) ,
                   ((λ G → funextD λ x → pr₁ (pr₂ (pr₂ (pr₂ (F x)))) (G x)) ,
                   ( λ G → funextD λ x → pr₁ (pr₂ (pr₂ (F x))) (G x)))))


Sigma-preserves-equiv : ∀ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k}
                        → ((x : A) → B x ≃ C x)
                        → (Σ[ x ∈ A ] B x) ≃ (Σ[ x ∈ A ] C x)
Sigma-preserves-equiv F = equiv-adjointify ((λ {(a , b) → a , pr₁ (F a) b}) ,
                      ((λ { (a , c) → a , (pr₁ (pr₂ (F a)) c)}) ,
                      ((λ {(a , c) → path-equiv-sigma (refl , (pr₁ (pr₂ (pr₂ (pr₂ (F a)))) c))}) ,
                      λ { (a , b) → path-equiv-sigma (refl , (pr₁ (pr₂ (pr₂ (F a))) b))})))



lemma4-2-11i : ∀ {i j} {A : Type i} {B : Type j}
               {f : A → B} (X : linv f)
               → (lcoh f X ≃ ((y : B) → _≡_ {_} {fib (pr₁ X) (pr₁ X y)} (f (pr₁ X y) , (pr₂ X) ((pr₁ X) y)) (y , refl)))
lemma4-2-11i {i} {j} {A} {B} {f} (g , η) = ((Sigma-Pi-swap {_} {_} {_} {B} {λ y → f (g y) ≡ y} {λ y → λ ε → ap g ε ≡ η (g y)})^ᵉ) oₑ equiv-fibres-to-Pi (λ y → (lemma4-2-5 (f (g y) , η (g y)) (y , refl) oₑ (Sigma-preserves-equiv λ p → transport (λ q → ((q ≡ η (g y)) ≃ (ap g p ≡ η (g y)))) (p-refl (ap g p) ^) erefl))^ᵉ)

lemma4-2-11ii : ∀ {i j} {A : Type i} {B : Type j}
                {f : A → B} (X : rinv f)
                → (rcoh f X ≃ ((x : A) → _≡_ {_} {fib f (f x)} ((pr₁ X) (f x) , (pr₂ X) (f x)) (x , refl)))
lemma4-2-11ii {i} {j} {A} {B} {f} (g , ε) = (Sigma-Pi-swap {_} {_} {_} {A} {λ x → g (f x) ≡ x} {λ x → λ η → ap f η ≡ ε (f x)}^ᵉ) oₑ equiv-fibres-to-Pi (λ x → (lemma4-2-5 (g (f x) , ε (f x)) (x , refl) oₑ (Sigma-preserves-equiv λ p → transport (λ q → (q ≡ ε (f x)) ≃ (ap f p ≡ ε (f x))) (p-refl (ap f p) ^) erefl)) ^ᵉ)


isEquiv-to-isContrmap : {i j : Level} {A : Type i} {B : Type j} {f : A → B}
                     → isEquiv f
                     → isContrmap f
isEquiv-to-isContrmap {_} {_} {A} {B} {f} (g , η , ε , τ) y = ((g y) , (ε y)) , (λ { (x , p) → pr₁ (lemma4-2-5 (g y , ε y) ( x , p) ^ᵉ) ((ap g p ^ ∘ η x) ,
                      transport (λ q → q ∘ p ≡ ε y) (apf-pq f (ap g p ^) (η x) ^) (transport (λ q → ((ap f q) ∘ (ap f (η x))) ∘ p ≡ ε y) (apf-p^ g p)
                      (transport (λ q → (q ∘ (ap f (η x))) ∘ p ≡ ε y) (ap-gf f g (p ^)) (transport (λ q → ((ap (f o g) (p ^)) ∘ q) ∘ p ≡ ε y) (τ x ^)
                      (transport (λ q → q ∘ p ≡ ε y) (homotopy-natural ε (p ^)) (transport (λ q → (ε y ∘ q) ∘ p ≡ ε y) (ap-id (p ^) ^) (ass-l (ε y) (p ^) p ∘ (p-to-pq^q (ε y) p) ^))) ))))})




lemma4-2-12 : ∀ {i j} {A : Type i} {B : Type j} {f : A → B}
              → isEquiv f → (X : rinv f)
              → isContr (rcoh f X)
lemma4-2-12 {i} {j} {A} {B} {f} F G = equiv-with-contr (lemma4-2-11ii G ^ᵉ) (contr-fibres-to-contr-Pi λ x → contr-has-contr-path-space (isEquiv-to-isContrmap F (f x) ))

ex3-4 : ∀ {i} (A : Type i)
        → isProp A ↔ isContr (A → A)
ex3-4 A = (λ F → id , λ f → funext λ x → F x (f x)) , λ { (f , F) x y → happly (F id) x ^ ∘ happly (F (λ _ → y)) x}

private
  ex3-5-i : ∀ {i} (A : Type i)
          → isProp A → (A → isContr A)
  ex3-5-i A F x = x , (λ y → F x y)

  ex3-5-ii : ∀ {i} (A : Type i)
             → (A → isContr A) → isProp A
  ex3-5-ii A F x y = (pr₂ (F x) x ^) ∘ pr₂ (F x) y

  ex3-5-iii : ∀ {i} (A : Type i)
            → ex3-5-i A o ex3-5-ii A ~ id
  ex3-5-iii A F = funextD λ x → isContr-is-prop _ _

  ex3-5-iv : ∀ {i} (A : Type i)
           → ex3-5-ii A o ex3-5-i A ~ id
  ex3-5-iv A F = funextD λ x → funextD λ y → props-are-sets F _ _ _ _ 


ex3-5 : ∀ {i} {A : Type i}
        → isProp A ≃ (A → isContr A)
ex3-5 {i} {A} = equiv-adjointify (ex3-5-i A , (ex3-5-ii A) , ((ex3-5-iii A) , (ex3-5-iv A)))

Sigma-associative : ∀ {i j k} {A : Type i} {B : A → Type j} {C : Σ[ x ∈ A ] B x → Type k}
                    → (Σ[ x ∈ A ] Σ[ y ∈ (B x) ] (C (x , y))) ≃ (Σ[ p ∈ (Σ[ x ∈ A ] B x) ] C p)
Sigma-associative = equiv-adjointify ((λ { (a , b , c) → (a , b) , c}) ,
                  ((λ { ((a , b) , c) → a , (b , c)}) ,
                  ((λ { ((a , b) , c) → refl}) ,
                  λ { (a , b , c) → refl})))


private
  Sigma-swapped : ∀ {i j k} {A : Type i} {B : Type j} {C : A → B → Type k}
                    → (Σ[ a ∈ A ] (Σ[ b ∈ B ] C a b)) ≃ (Σ[ b ∈ B ] (Σ[ a ∈ A ] C a b))
  Sigma-swapped = equiv-adjointify ((λ {(a , b , c) → b , (a , c)}) ,
                ((λ { (b , a , c) → a , (b , c)}) ,
                ((λ { (b , a , c) → path-equiv-sigma (refl , refl)}) ,
                λ { (a , b , c) → path-equiv-sigma (refl , refl)})))


  isEquiv-swapped : ∀ {i j} {A : Type i} {B : Type j}
                    (f : A → B)
                    → (isEquiv f) ≃ (Σ[ g ∈ (B → A) ] (Σ[ ε ∈ (f o g ~ id) ] (Σ[ η ∈ (g o f ~ id) ] ((x : A) → ap f (η x) ≡ ε (f x)))))
  isEquiv-swapped f = equiv-fibres-to-equiv-sigma λ g → Sigma-swapped





  isEquiv-equiv-rcoh : ∀ {i j} {A : Type i} {B : Type j}
                       (f : A → B)
                       → (isEquiv f) ≃ (Σ[ u ∈ (rinv f)] (rcoh f (pr₁ u , pr₂ u)))
  isEquiv-equiv-rcoh {i} {j} {A} {B} f = isEquiv-swapped f oₑ Sigma-associative


qinv-to-isContr-rinv : ∀ {i j} {A : Type i} {B : Type j} {f : A → B}
                       → qinv f
                       → isContr (rinv f)
qinv-to-isContr-rinv {i} {j} {A} {B} {f} F = equiv-with-contr (equiv-fibres-to-equiv-sigma (λ g → funext-equiv {_} {_} {_} {_} {f o g} {id})) (isEquiv-to-isContrmap (isequiv-adjointify (lemma4-2-8i F)) id)
lemma4-2-9i = qinv-to-isContr-rinv

qinv-to-isContr-linv : ∀ {i j} {A : Type i} {B : Type j} {f : A → B}
                       → qinv f
                       → isContr (linv f)
qinv-to-isContr-linv {i} {j} {A} {B} {f} F =  equiv-with-contr (equiv-fibres-to-equiv-sigma (λ g → funext-equiv {_} {_} {_} {_} {g o f} {id})) (isEquiv-to-isContrmap (isequiv-adjointify (lemma4-2-8ii F)) id)
lemma4-2-9-ii = qinv-to-isContr-linv

isEquiv-is-prop : ∀ {i j} {A : Type i} {B : Type j}
                  (f : A → B)
                  → isProp (isEquiv f)
isEquiv-is-prop {i} {j} {A} {B} f = pr₁ ((ex3-5 {_} {isEquiv f}) ^ᵉ) λ { F → equiv-with-contr (isEquiv-equiv-rcoh f ^ᵉ)
                (contr-fibres-to-contr-Sigma (λ { (g , u) → lemma4-2-12 F (g , u)})  (qinv-to-isContr-rinv (isEquiv-to-qinv F)))}



-- The following need to be sorted and put in their correct location
-- Lemma 4.4.4
isContrmap-is-prop : ∀ {i j} {A : Type i} {B : Type j}
                     (f : A → B)
                     → isProp (isContrmap f)
isContrmap-is-prop f =
  prop-fibres-Pi-is-prop λ b → isContr-is-prop

-- Lemma 4.4.5
isContrmap-equiv-isEquiv : ∀ {i j} {A : Type i} {B : Type j}
                     (f : A → B)
                     → isContrmap f ≃ isEquiv f
isContrmap-equiv-isEquiv f =
  props-equiv
   (isContrmap-is-prop f)
   (isEquiv-is-prop f)
   isContrmap-to-isEquiv
   isEquiv-to-isContrmap

-- Theorem 4.3.2
isBiinv-is-prop : ∀ {i j} {A : Type i} {B : Type j}
                  (f : A → B)
                  → isProp (isBiinv f)
isBiinv-is-prop f H H' =
  contr-are-props
    (contr-fibres-to-contr-Sigma
      (λ x → qinv-to-isContr-rinv (isBiinv-to-qinv H))
      (qinv-to-isContr-linv (isBiinv-to-qinv H)))
    H
    H'
-- Corollary 4.3.3
isBiinv-equiv-isEquiv : ∀ {i j} {A : Type i} {B : Type j}
                        (f : A → B)
                        → isBiinv f ≃ isEquiv f
isBiinv-equiv-isEquiv f =
  props-equiv
    (isBiinv-is-prop f)
    (isEquiv-is-prop f)
    (qinv-to-ishae o isBiinv-to-qinv)
    (qinv-to-isBiinv o isEquiv-to-qinv)

-- * More results
-- The inverse of a composite of equivalences is the composites
-- inverses.

inv-of-comp-of-eqv : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
                     (f : A ≃ B) (g : B ≃ C)
                     → (f oₑ g) ^ᵉ ≡ (g ^ᵉ) oₑ (f ^ᵉ)
inv-of-comp-of-eqv f g =
  fibres-props-eq
    isEquiv-is-prop
    ((f oₑ g) ^ᵉ)
    ((g ^ᵉ) oₑ (f ^ᵉ))
    refl
