{-# OPTIONS --without-K #-}
module UniAgda.core.prop-set-properties where

open import UniAgda.core.axioms public
open import UniAgda.core.path-spaces public

unit-is-set : isSet Unit
unit-is-set x y = transport (λ X → (p q : X) → p ≡ q) (ua (thm2-8-1 x y) ^) λ { tt tt → refl}
ex3-1-2 = unit-is-set

empty-is-set : isSet Empty
empty-is-set () y
ex3-1-3 = empty-is-set

private
  nat-equiv-to-id : (m n : ℕ) → (m ≡ n) ≡ nat-code m n
  nat-equiv-to-id m n = ua {_} {_} {_} (thm2-13-1 m n)


ℕ-is-set : isSet ℕ
ℕ-is-set zero zero = transport (λ X → (p q : X) → p ≡ q) (nat-equiv-to-id zero zero ^) λ { tt tt → refl}
ℕ-is-set zero (suc n) = transport (λ X → (p q : X) → p ≡ q) (nat-equiv-to-id zero (suc n) ^) λ { () q}
ℕ-is-set (suc m) zero = transport (λ X → (p q : X) → p ≡ q) (nat-equiv-to-id (suc m) zero ^) λ { () q}
ℕ-is-set (suc m) (suc n) = transport (λ X → (p q : X) → p ≡ q) (nat-equiv-to-id (suc m) (suc n) ^) (transport (λ X → (p q : X) → p ≡ q) (nat-equiv-to-id m n) (ℕ-is-set m n))


{- Product of sets is a set -}
private
  path-prod-equiv-to-id : {i j : Level} {A : Type i} {B : Type j}
                   (x y : A × B)
                   → (x ≡ y) ≡ ((pr₁ x ≡ pr₁ y) × (pr₂ x ≡ pr₂ y))
  path-prod-equiv-to-id x y = ua path-prod-equiv


prod-of-sets-is-set : ∀ {i j} {A : Type i} {B : Type j}
                      → (isSet A) → (isSet B)
                      → (isSet (A × B))
prod-of-sets-is-set H₁ H₂ x y = transport (λ X → (p q : X) → p ≡ q) (path-prod-equiv-to-id x y ^) λ { (a , b) (a' , b') → path-equiv-prod (H₁ (pr₁ x) (pr₁ y) a a' , H₂ (pr₂ x) (pr₂ y) b b')}


{-Functions between sets form a set-}
private
  funext-to-id : {i j : Level} {A : Type i} {B : Type j} {f g : A → B}
                 → (f ≡ g) ≡ (f ~ g)
  funext-to-id = ua funext-equiv

-- fibs-are-sets-PI-is-set : ∀ {i j} {A : Type i} {B : A → Type j}
--                           → ((x : A) → (isSet (B x)))
--                           → (isSet ((x : A) → B x))
-- fibs-are-sets-PI-is-set H f g p q = {!!}




func-of-sets-is-set : ∀ {i j} {A : Type i} {B : Type j}
                      → (isSet B)
                      → (isSet (A → B))
func-of-sets-is-set H f g = transport (λ X → (p q : X) → p ≡ q) (funext-to-id ^) λ { p q → funextD λ x → H (f x) (g x) (p x) (q x)}

x-in-prop-equiv-unit : {i : Level} {P : Type i}
                       → isProp P → P
                       → P ≃ Unit
x-in-prop-equiv-unit X x₀ = equiv-adjointify ((λ x → tt) , ((λ x → x₀) , ((λ { tt → refl}) , λ x → X x₀ x)))
lemma3-3-2 = x-in-prop-equiv-unit

props-equiv : {i j : Level} {P : Type i} {Q : Type j}
         → isProp P → isProp Q → (P → Q) → (Q → P)
         → P ≃ Q
props-equiv {i} {j} {P} {Q} X Y f g = equiv-adjointify (f , g , ((λ y → Y ((f o g) y) y) , λ x → X ((g o f) x) x))
lemma3-3-3 = props-equiv

lemma3-3-4-help : {i : Level} {A : Type i} {f : (x y : A) → x ≡ y} {x : A}
                  → (y z : A) (p : y ≡ z)
                  → (f x y) ∘ p ≡ f x z
lemma3-3-4-help {_} {A} {f} {x} y z p = lemma2-11-2i x p (f x y) ^ ∘ apD (λ y → f x y) p

props-are-sets : {i : Level} {A : Type i}
             → isProp A → isSet A
props-are-sets {i} {A} f x y p q = pq=s-to-q=p^s (f x x) p (f x y) (lemma3-3-4-help {_} {_} {f} {x} x y p) ∘ pq=s-to-q=p^s {_} {A} {_} {_} {_} (f x x) q (f x y) (lemma3-3-4-help {_} {_} {f} {x} x y q) ^


lemma3-3-4 = props-are-sets

isProp-is-prop : {i : Level}
                  (A : Type i)
                  → isProp (isProp A)
isProp-is-prop A f g = funextD λ x → funextD λ y → props-are-sets f x y (f x y) (g x y)
lemma3-3-5i = isProp-is-prop

fibres-props-eq : {i j : Level} {A : Type i} {P : A → Type j}
                   → ((x : A) → isProp (P x)) → (u v : Σ[ x ∈ A ] (P x)) → (pr₁ u ≡ pr₁ v)
                   → u ≡ v
fibres-props-eq {_} {_} {A} {P} X u v p = path-equiv-sigma u v (p , (X (pr₁ v) (transport P p (pr₂ u)) (pr₂ v)))
lemma3-5-1 = fibres-props-eq
private
  helper : ∀ {i} {A : Type i}
           → (f : isSet {i} A) → (x y : A) → (p q q' : x ≡ y) → (r : q ≡ q')
           → (f x y p q) ∘ r ≡ f x y p q'
  helper f x y p q q' r = (lemma2-11-2i _ r (f x y p q) ^ ) ∘ apD (λ q → f x y p q) r



sets-are-1types : ∀ {i} {A : Type i}
                  → isSet {i} A → is1type {i} A
sets-are-1types f x y p q r s = pq=s-to-q=p^s (f x y p p) r (f x y p q) (helper f x y p p q r) ∘ (pq=s-to-q=p^s (f x y p p) s (f x y p q) (helper f x y p p q s)) ^



isSet-is-prop : {i : Level}
                (A : Type i)
                → isProp (isSet A)
isSet-is-prop A f g = funextD λ {x → funextD λ x₁ → funextD λ x₂ → funextD λ x₃ → sets-are-1types f _ _ _ _ _ _}


private
  path-equiv-sigma-to-id : {i j : Level} {A : Type i} {P : A → Type j}
                           {w w' : Σ[ x ∈ A ] (P x)}
                           → (w ≡ w') ≡ (Σ[ p ∈ (pr₁ w ≡ pr₁ w') ] (transport P p (pr₂ w) ≡ (pr₂ w')))
  path-equiv-sigma-to-id  = ua (thm2-7-2 _ _)



prop-fibres-totalspace-set : ∀ {i j} {A : Type i} {P : A → Type j}
                             → isSet A → ((a : A) → isProp (P a))
                             → isSet (Σ[ a ∈ A ] (P a))
prop-fibres-totalspace-set {i} {j} {A} {P} H f X Y = transport (λ Z → (p q : Z) → p ≡ q) (path-equiv-sigma-to-id ^) λ { (a , b) (a' , b') → path-equiv-sigma _ _ (H _ _ _ _ , props-are-sets (f (pr₁ Y))  _ _ _ _)}

-- foo : ∀ {i j} {A : Type i} {P : A → Type j}
--       → isSet A → isProp ((a : A) → P a) → isSet (Σ[ a ∈ A ] P a)
-- foo {i} {j} {A} {P} H X (a , b) (a' , b') = transport (λ Z → (p q : Z) → p ≡ q) (path-equiv-sigma-to-id ^) λ { (p , b) (q , c) → path-equiv-sigma _ _ (H _ _ _ _ , {!sets-are-1types H _  !})}

foo : ∀ {i j} → {A : Type i} {B : A → Type j}
      → isSet A → ((a : A) → isSet (B a))
      → isSet (Σ[ a ∈ A ] B a )
foo {_} {_} {A} {B} X f (a , H) (b , H') = transport (λ Z → (p q : Z) → p ≡ q) (path-equiv-sigma-to-id ^) λ { (p , U) (q , V) → path-equiv-sigma _ _ ((X _ _ _ _) , (f b _ _ _ _))}


prop-fibres-Pi-is-prop : ∀ {i j} {A : Type i} {B : A → Type j}
                         → ((x : A) → isProp (B x))
                         → isProp ((x : A) → B x)
prop-fibres-Pi-is-prop F f g = funextD λ x → F x (f x) (g x)


Unit-is-contr : isContr Unit
Unit-is-contr = tt , (λ { tt → refl})

Unit-is-prop : isProp Unit
Unit-is-prop tt tt = refl

contr-to-pointed-prop : ∀ {i} {A : Type i}
                        → isContr A
                        → A × isProp A
contr-to-pointed-prop (a , F) = a , (λ x y → F x ^ ∘ F y)

contr-are-props : ∀ {i} {A : Type i}
                  → isContr A
                  → isProp A
contr-are-props X = pr₂ (contr-to-pointed-prop X)

pointed-prop-to-contr : ∀ {i} {A : Type i}
                        → A × isProp A
                        → isContr A
pointed-prop-to-contr (a , F) = a , (F a)


contr-equiv-to-Unit : ∀ {i} {A : Type i}
                      → isContr A
                      → A ≃ Unit
contr-equiv-to-Unit (a , F) = equiv-adjointify ((λ _ → tt) ,
                                               ((λ { tt → a}) ,
                                               ((λ { tt → refl}) ,
                                               λ x → F x)))

equiv-with-prop : ∀ {i j} {A : Type i} {B : Type j}
                  → A ≃ B → isProp A
                  → isProp B
equiv-with-prop (f , g , α , β , γ) F x y = (((ap f (F (g y) (g x))) ∘ β x) ^) ∘ β y


equiv-Unit-to-contr : ∀ {i} {A : Type i}
                      → A ≃ Unit
                      → isContr A
equiv-Unit-to-contr (f , g , α , β , γ) = pointed-prop-to-contr ((g tt) , (equiv-with-prop ((f , g , α , β , γ) ^ᵉ) Unit-is-prop))


isContr-is-prop : ∀ {i} {A : Type i}
                  → isProp (isContr A)
isContr-is-prop (a , p) (a' , p') = path-equiv-sigma _ _ ((p a') , prop-fibres-Pi-is-prop (λ x → props-are-sets (contr-are-props (a , p)) _ _) _ _)

private
  lemma4-2-5i : ∀ {i j} {A : Type i} {B : Type j}
                (f : A → B) (y : B) (X Y : fib f y)
                → (X ≡ Y) → (Σ[ γ ∈ (pr₁ X ≡ pr₁ Y) ] ((ap f γ) ∘ pr₂ Y ≡ pr₂ X))
  lemma4-2-5i f y X .X refl = refl , refl

  lemma4-2-5ii : ∀ {i j} {A : Type i} {B : Type j}
                 (f : A → B) (y : B) (X Y : fib f y)
                 → (Σ[ γ ∈ (pr₁ X ≡ pr₁ Y) ] ((ap f γ) ∘ pr₂ Y ≡ pr₂ X)) → X ≡ Y
  lemma4-2-5ii f y (a , p) (b , q) (s , t) = path-equiv-sigma _ _ (s , thm2-11-3 f (λ _ → y) s p ∘ p=rq-to-r^p=q (p ∘ ap (λ _ → y) s) q (ap f s) ((transport (λ q → p ∘ q ≡ p) (ap-const y ^) (p-refl p) ) ∘ t ^) )

--   lemma4-2-5iii : ∀ {i j} {A : Type i} {B : Type j}
--                    (f : A → B) (y : B) (X Y : fib f y)
--                    → (lemma4-2-5i f y X Y o lemma4-2-5ii f y X Y) ~ id
--   lemma4-2-5iii f y (a , p) (a' , p') (q , s) = path-equiv-sigma _ _ ({! ((lemma4-2-5i f y (a , p) (a' , p') o
--         lemma4-2-5ii f y (a , p) (a' , p'))
--        (q , s))
-- !} , {!!})


sigma-help : ∀ {i j } {A : Type i} {B : A → Type j} {C : A → Type j}
      → ((x : A) → (B x ≃ C x))
      → (Σ[ x ∈ A ] B x) ≃ (Σ[ x ∈ A ] C x)
sigma-help F = equiv-adjointify ((λ { (a , b) → a , pr₁ (F a) b}) ,
           (λ { (a , c) → a , (pr₁ (pr₂ (F a)) c)}) ,
           ((λ { (a , c) → path-equiv-sigma _ _ (refl , (pr₁ (pr₂ (pr₂ (pr₂ (F a)))) c ))}) ,
           λ { (a , b) → path-equiv-sigma _ _ (refl , (pr₁ (pr₂ (pr₂ (F a))) b))}))


last-helper : ∀ {i} {A : Type i} {x y : A} {p p' : x ≡ y}
              → (p ≡ p') ≃ (p' ≡ p)
last-helper {i} {A} {x} {y} {p} {p'} = equiv-adjointify ((λ α → α ^) ,
            (λ β → β ^) ,
            (λ { refl → refl}) ,
            λ { refl → refl})



lemma4-2-5 : ∀ {i j} {A : Type i} {B : Type j}
             (f : A → B) (y : B) (X Y : fib f y)
             → (X ≡ Y) ≃ (Σ[ γ ∈ (pr₁ X ≡ pr₁ Y) ] ((ap f γ) ∘ pr₂ Y ≡ pr₂ X))
lemma4-2-5 f y (x , p) (x' , p') = sigma-help (λ { refl → last-helper}) oₑ thm2-7-2 (x , p) (x' , p') 

-- lemma4-2-11i : ∀ {i j} {A : Type i} {B : Type j}
--                (f : A → B) (X : linv f)
--                → lcoh f X ≃ ((y : B) → (f (pr₁ X y) , (pr₂ X) ((pr₁ X) y)) ≡ (y , refl))
-- lemma4-2-11i {i} {j} {A} {B} f X = equiv-adjointify ((λ x y → {!!})
--   , {!!})
