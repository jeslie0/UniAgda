{-# OPTIONS --without-K #-}
module UniAgda.core.prop-set-properties where

open import UniAgda.core.axioms public
open import UniAgda.core.path-spaces public


{- Results about sets -}

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
  funextD-to-id : {i j : Level} {A : Type i} {B : A → Type j} {f g : (x : A) → B x}
                 → (f ≡ g) ≡ (f ~ g)
  funextD-to-id = ua funextD-equiv

fibs-are-sets-PI-is-set : ∀ {i j} {A : Type i} {B : A → Type j}
                          → ((x : A) → (isSet (B x)))
                          → (isSet ((x : A) → B x))
fibs-are-sets-PI-is-set H f g = transport (λ Z → (p q : Z) → p ≡ q) (funextD-to-id ^) λ { p q → funextD λ x → H x _ _ _ _}


func-of-sets-is-set : ∀ {i j} {A : Type i} {B : Type j}
                      → (isSet B)
                      → (isSet (A → B))
func-of-sets-is-set H f g = transport (λ X → (p q : X) → p ≡ q) (funextD-to-id ^) λ { p q → funextD λ x → H (f x) (g x) (p x) (q x)}



private
  helper : ∀ {i} {A : Type i}
           → (f : isSet {i} A) → (x y : A) → (p q q' : x ≡ y) → (r : q ≡ q')
           → (f x y p q) ∘ r ≡ f x y p q'
  helper f x y p q q' r = (lemma2-11-2i _ r (f x y p q) ^ ) ∘ apD (λ q → f x y p q) r


sets-are-1types : ∀ {i} {A : Type i}
                  → isSet {i} A → is1type {i} A
sets-are-1types f x y p q r s = pq=r-to-q=p^r (f x y p p) r (f x y p q) (helper f x y p p q r) ∘ (pq=r-to-q=p^r (f x y p p) s (f x y p q) (helper f x y p p q s)) ^





{- Results about propositions -}


Unit-is-prop : isProp Unit
Unit-is-prop tt tt = refl

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
props-are-sets {i} {A} f x y p q = pq=r-to-q=p^r (f x x) p (f x y) (lemma3-3-4-help {_} {_} {f} {x} x y p) ∘ pq=r-to-q=p^r {_} {A} {_} {_} {_} (f x x) q (f x y) (lemma3-3-4-help {_} {_} {f} {x} x y q) ^


lemma3-3-4 = props-are-sets

isProp-is-prop : {i : Level}
                  (A : Type i)
                  → isProp (isProp A)
isProp-is-prop A f g = funextD λ x → funextD λ y → props-are-sets f x y (f x y) (g x y)
lemma3-3-5i = isProp-is-prop

fibres-props-eq : {i j : Level} {A : Type i} {P : A → Type j}
                   → ((x : A) → isProp (P x)) → (u v : Σ[ x ∈ A ] (P x)) → (pr₁ u ≡ pr₁ v)
                   → u ≡ v
fibres-props-eq {_} {_} {A} {P} X u v p = path-equiv-sigma (p , (X (pr₁ v) (transport P p (pr₂ u)) (pr₂ v)))
lemma3-5-1 = fibres-props-eq


isSet-is-prop : {i : Level}
                (A : Type i)
                → isProp (isSet A)
isSet-is-prop A f g = funextD λ {x → funextD λ x₁ → funextD λ x₂ → funextD λ x₃ → sets-are-1types f _ _ _ _ _ _}


private
  path-equiv-sigma-to-id : {i j : Level} {A : Type i} {P : A → Type j}
                           {w w' : Σ[ x ∈ A ] (P x)}
                           → (w ≡ w') ≡ (Σ[ p ∈ (pr₁ w ≡ pr₁ w') ] (transport P p (pr₂ w) ≡ (pr₂ w')))
  path-equiv-sigma-to-id  = ua (thm2-7-2)



prop-fibres-totalspace-set : ∀ {i j} {A : Type i} {P : A → Type j}
                             → isSet A → ((a : A) → isProp (P a))
                             → isSet (Σ[ a ∈ A ] (P a))
prop-fibres-totalspace-set {i} {j} {A} {P} H f X Y = transport (λ Z → (p q : Z) → p ≡ q) (path-equiv-sigma-to-id ^) λ { (a , b) (a' , b') → path-equiv-sigma (H _ _ _ _ , props-are-sets (f (pr₁ Y))  _ _ _ _)}


prop-fibres-Pi-is-prop : ∀ {i j} {A : Type i} {B : A → Type j}
                         → ((x : A) → isProp (B x))
                         → isProp ((x : A) → B x)
prop-fibres-Pi-is-prop F f g = funextD λ x → F x (f x) (g x)



equiv-with-prop : ∀ {i j} {A : Type i} {B : Type j}
                  → A ≃ B → isProp A
                  → isProp B
equiv-with-prop (f , g , α , β , γ) F x y = (((ap f (F (g y) (g x))) ∘ β x) ^) ∘ β y


equiv-with-set : ∀ {i j} {A : Type i} {B : Type j}
                 → A ≃ B → isSet A
                 → isSet B
equiv-with-set (f , g , α , β , γ) F x y = equiv-with-prop {_} {_} {g x ≡ g y} {x ≡ y} (((ap g) , (thm2-11-1 (isequiv-adjointify (f , (α , β))))) ^ᵉ) (F (g x) (g y))






{- Results about contractibility -}




Unit-is-contr : isContr Unit
Unit-is-contr = tt , (λ { tt → refl})


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



equiv-Unit-to-contr : ∀ {i} {A : Type i}
                      → A ≃ Unit
                      → isContr A
equiv-Unit-to-contr (f , g , α , β , γ) = pointed-prop-to-contr ((g tt) , (equiv-with-prop ((f , g , α , β , γ) ^ᵉ) Unit-is-prop))

equiv-with-contr : ∀ {i j} {A : Type i} {B : Type j}
                   → A ≃ B → isContr A
                   → isContr B
equiv-with-contr X Y = equiv-Unit-to-contr (contr-equiv-to-Unit Y oₑ (X ^ᵉ) )

isContr-is-prop : ∀ {i} {A : Type i}
                  → isProp (isContr A)
isContr-is-prop (a , p) (a' , p') = path-equiv-sigma ((p a') , prop-fibres-Pi-is-prop (λ x → props-are-sets (contr-are-props (a , p)) _ _) _ _)

contr-fibres-to-contr-Pi : ∀ {i j} {A : Type i} {P : A → Type j}
                           → ((x : A) → isContr (P x))
                           → isContr ((x : A) → P x)
contr-fibres-to-contr-Pi F = pointed-prop-to-contr ((λ x → pr₁ (F x)) , (prop-fibres-Pi-is-prop (λ x → contr-are-props (F x))))


Sigma-path-is-contr : ∀ {i} {A : Type i}
                      (a : A)
                      → isContr (Σ[ x ∈ A ] (a ≡ x))
Sigma-path-is-contr a = (a , refl) , (λ { (x , p) → path-equiv-sigma (p , (lemma2-11-2i a p refl))})


lemma3-11-9i : ∀ {i j} {A : Type i} {P : A → Type j}
               → ((x : A) → isContr (P x))
               → (Σ[ x ∈ A ] P x) ≃ A
lemma3-11-9i F = equiv-adjointify ((λ x → pr₁ x) , ((λ x → x , (pr₁ (F x))) , ((λ x → refl) , (λ { (a , b) → path-equiv-sigma (refl , (contr-are-props (F a) _ _))}))))



contr-base-equiv-fibres : ∀ {i j} {A : Type i} {P : A → Type j}
                        (X : isContr A)
                        → (x : A) → (Σ[ x ∈ A ] P x) ≃ (P x)
contr-base-equiv-fibres {i} {j} {A} {P} (a , F) x = equiv-adjointify ((λ { (a' , p) → transport P (F a' ^ ∘ F x) p}) ,
                        (λ u → x , u) ,
                        ((λ u → transport (λ q → transport P q u ≡ u) (p^p (F x) ^) refl ) ,
                        λ { (a , u) → path-equiv-sigma ((F x ^ ∘ F a) , (tr-pq  (F a ^ ∘ F x) (F x ^ ∘ F a) u ^ ∘
                        transport (λ q → transport (λ v → P v) ((F a ^ ∘ F x) ∘ q) u ≡ u) (pq-^-to-q^p^ (F a ^) (F x) ∘
                        p=q-to-rp=rq (p^^=p (F a) ) (F x ^) ) (transport (λ q → (transport P q u) ≡ u) (pp^ (F a ^ ∘ F x) ^) refl) ))}))

lemma3-11-9ii : ∀ {i j} {A : Type i} {P : A → Type j}
                (X : isContr A)
                → (Σ[ x ∈ A ] P x) ≃ (P (pr₁ X))
lemma3-11-9ii {i} {j} {A} {P} (a , F) = contr-base-equiv-fibres (a , F) a

-- ((λ { (x , u) → transport P (F x ^) u}) ,
--               (λ x → a , x) ,
--               ((λ x → {!!}) ,
--               (λ { (x , p) → path-equiv-sigma ((F x) , (tr-pq (F x ^) (F x) p ^ ∘ transport (λ q → transport P q p ≡ p) (p^p (F x) ^) refl))})))



contr-fibres-to-contr-Sigma : ∀ {i j} {A : Type i} {P : A → Type j}
                              → ((x : A) → isContr (P x)) → (isContr A)
                              → isContr (Σ[ x ∈ A ] P x)
contr-fibres-to-contr-Sigma F X = equiv-with-contr (lemma3-11-9i F ^ᵉ) X

{- Results needed for lemma4-2-5. Unsure where to put -}
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
lemma4-2-5 {i} {j} {A} {B} {f} {y} (x , p) (x' , p') = equiv-fibres-to-equiv-sigma (λ { refl → p=p'-equiv-p'=p}) oₑ thm2-7-2 
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
lemma4-2-11i {i} {j} {A} {B} {f} (g , η) = equiv-fibres-to-Pi (λ y → ((Sigma-preserves-equiv λ p → transport (λ q → ((q ≡ η (g y)) ≃ (ap g p ≡ η (g y)))) (p-refl (ap g p) ^) erefl)
             oₑ lemma4-2-5 (f (g y) , η (g y)) (y , refl))^ᵉ) oₑ ((Sigma-Pi-swap {_} {_} {_} {B} {λ y → f (g y) ≡ y} {λ y → λ ε → ap g ε ≡ η (g y)})^ᵉ)

lemma4-2-11ii : ∀ {i j} {A : Type i} {B : Type j}
                {f : A → B} (X : rinv f)
                → (rcoh f X ≃ ((x : A) → _≡_ {_} {fib f (f x)} ((pr₁ X) (f x) , (pr₂ X) (f x)) (x , refl)))
lemma4-2-11ii {i} {j} {A} {B} {f} (g , ε) = equiv-fibres-to-Pi (λ x → ((Sigma-preserves-equiv λ p → transport (λ q → (q ≡ ε (f x)) ≃ (ap f p ≡ ε (f x))) (p-refl (ap f p) ^) erefl)
  oₑ lemma4-2-5 (g (f x) , ε (f x)) (x , refl)) ^ᵉ) oₑ (Sigma-Pi-swap {_} {_} {_} {A} {λ x → g (f x) ≡ x} {λ x → λ η → ap f η ≡ ε (f x)}^ᵉ)


isEquiv-to-isContrmap : {i j : Level} {A : Type i} {B : Type j} {f : A → B}
                     → isEquiv f
                     → isContrmap f
isEquiv-to-isContrmap {_} {_} {A} {B} {f} (g , η , ε , τ) y = ((g y) , (ε y)) , (λ { (x , p) → pr₁ (lemma4-2-5 (g y , ε y) ( x , p) ^ᵉ) ((ap g p ^ ∘ η x) ,
                      transport (λ q → q ∘ p ≡ ε y) (apf-pq f (ap g p ^) (η x) ^) (transport (λ q → ((f [ q ]) ∘ (f [ η x ])) ∘ p ≡ ε y) (apf-p^ g p)
                      (transport (λ q → (q ∘ (ap f (η x))) ∘ p ≡ ε y) (ap-gf f g (p ^)) (transport (λ q → (((f o g) [ p ^ ]) ∘ q) ∘ p ≡ ε y) (τ x ^)
                      (transport (λ q → q ∘ p ≡ ε y) (homotopy-natural ε (p ^)) (transport (λ q → (ε y ∘ q) ∘ p ≡ ε y) (ap-id (p ^) ^) (ass-l (ε y) (p ^) p ∘ (p-to-pq^q (ε y) p) ^))) ))))})


contr-has-contr-path-space : ∀ {i} {A : Type i} {x y : A}
                             → isContr A → isContr (x ≡ y)
contr-has-contr-path-space {i} {A} {x} {y} (a , F) = (F x) ^ ∘ F y , λ { refl → p^p (F x)}





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
  isEquiv-equiv-rcoh {i} {j} {A} {B} f = Sigma-associative oₑ isEquiv-swapped f


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

-- (Sigma-associative {_} {_} {_} {_} {_} {λ { (g , η) →
                -- Σ[ ε ∈ (f o g ~ id) ] ((x : A) → ap f (η x) ≡ ε (f x))}} ^ᵉ) (contr-fibres-to-contr-Sigma (λ { (g , η) → {!!}}) {!!}) }

-- λ { x → pr₁ (Sigma-associative) {!!} }
