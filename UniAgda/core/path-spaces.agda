{-

This file contains data on how the path spaces act in each of the data types we defined.

-}


{-# OPTIONS --without-K --safe #-}
module UniAgda.core.path-spaces where

open import UniAgda.core.equivalences public

{- Paths in Sigma types -}

path-equiv-prod : {i j : Level} {A : Type i} {B : Type j}
                  {x y : A × B}
                  → (pr₁ x ≡ pr₁ y) × (pr₂ x ≡ pr₂ y) → x ≡ y
path-equiv-prod {i} {j} {A} {B} {x = _ , _} {y = _ , _} (refl , refl) = refl

path-prod : {i j : Level} {A : Type i} {B : Type j}
            {x y : A × B}
            → x ≡ y → (pr₁ x ≡ pr₁ y) × (pr₂ x ≡ pr₂ y)
path-prod refl = refl , refl

private
  hom₁ : {i j : Level} {A : Type i} {B : Type j}
         {x y : A × B}
         → (path-equiv-prod o path-prod {i} {j} {A} {B} {x} {y}) ~ id
  hom₁ {x = _ , _} {y = _ , _} refl = refl

  hom₂ : {i j : Level} {A : Type i} {B : Type j}
         {x y : A × B}
         → (path-prod o path-equiv-prod {i} {j} {A} {B} {x} {y}) ~ id
  hom₂ {x = _ , _} {y = _ , _} (refl , refl) = refl


thm2-6-2 : {i j : Level} {A : Type i} {B : Type j}
           {x y : A × B}
           → isEquiv (path-prod {i} {j} {A} {B} {x} {y})
thm2-6-2 {x = _ , _} {y = _ , _} = isequiv-adjointify (path-equiv-prod , hom₂ , hom₁)

path-prod-equiv : {i j : Level} {A : Type i} {B : Type j}
            {x y : A × B}
            → (x ≡ y) ≃ ((pr₁ x ≡ pr₁ y) × (pr₂ x ≡ pr₂ y))
path-prod-equiv = path-prod , thm2-6-2

-- Sigma types

path-sigma : {i j : Level} {A : Type i} {P : A → Type j}
             {w w' : Σ[ x ∈ A ] (P x)}
             → (w ≡ w') → (Σ[ p ∈ (pr₁ w ≡ pr₁ w') ] (transport P p (pr₂ w) ≡ (pr₂ w')))
path-sigma {i} {j} {A} {P} {w} {.w} refl = refl , refl

path-equiv-sigma : {i j : Level} {A : Type i} {P : A → Type j}
                   {w w' : Σ[ x ∈ A ] (P x)}
                   → (Σ[ p ∈ (pr₁ w ≡ pr₁ w') ] (transport P p (pr₂ w) ≡ (pr₂ w'))) → w ≡ w'
path-equiv-sigma {_} {_} {A} {P} {a , b} {.(pr₁ {_} {_} {A} {P} (a , b)) , .b} (refl , refl) = refl

private
  hom₃ : {i j : Level} {A : Type i} {P : A → Type j}
         {w w' : Σ[ x ∈ A ] (P x)}
         → path-sigma o path-equiv-sigma {_} {_} {A} {P} {w} {w'} ~ id
  hom₃ {i} {j} {A} {P} {w = _ , _} {w' = _ , _} (refl , refl) =  refl

  hom₄ : {i j : Level} {A : Type i} {P : A → Type j}
         {w w' : Σ[ x ∈ A ] (P x)}
         → path-equiv-sigma o path-sigma {_} {_} {A} {P} {w} {w'} ~ id
  hom₄ {i} {j} {A} {P} {a , b} .{a , b} refl = refl

thm2-7-2 : {i j : Level} {A : Type i} {P : A → Type j}
           {w w' : Σ[ x ∈ A ] (P x)}
           → (w ≡ w') ≃ (Σ[ p ∈ (pr₁ w ≡ pr₁ w') ] (transport P p (pr₂ w) ≡ (pr₂ w')))
thm2-7-2 {_} {_} {A} {P} {w} {w'} = equiv-adjointify (path-sigma , path-equiv-sigma , hom₃ , hom₄)

cor2-7-3 : {i j : Level} {A : Type i} {P : A → Type j}
           (z : Σ[ x ∈ A ] (P x))
           → z ≡ (pr₁ z , pr₂ z)
cor2-7-3 {i} {j} {A} {P} z = path-equiv-sigma {_} {_} {A} {P} {z} {pr₁ z , pr₂ z} (refl , refl)


{- paths in the unit type -}

thm2-8-1i : (x y : Unit)
            → (x ≡ y) → Unit
thm2-8-1i x y p = tt

thm2-8-1ii : (x y : Unit)
            → Unit → (x ≡ y)
thm2-8-1ii tt tt X = refl

private
  hom₁-unit : (x y : Unit)
         → thm2-8-1i x y o thm2-8-1ii x y ~ id
  hom₁-unit tt tt tt = refl

  hom₂-unit : (x y : Unit)
         → thm2-8-1ii x y o thm2-8-1i x y ~ id
  hom₂-unit tt .tt refl = refl

thm2-8-1 : (x y : Unit)
           → (x ≡ y) ≃ Unit
thm2-8-1 x y = equiv-adjointify ((thm2-8-1i x y) , (thm2-8-1ii x y) , hom₁-unit x y , hom₂-unit x y)


{- paths in ℕ type -}

nat-code : ℕ → ℕ → Type lzero
nat-code zero zero = Unit
nat-code zero (suc m) = Empty
nat-code (suc n) zero = Empty
nat-code (suc n) (suc m) = nat-code n m

nat-r : (n : ℕ) → nat-code n n
nat-r zero = tt
nat-r (suc n) = nat-r n

nat-encode : (m n : ℕ) → m ≡ n → nat-code m n
nat-encode m n p = p # (nat-r m)

nat-decode : (m n : ℕ) → nat-code m n → m ≡ n
nat-decode zero zero x = refl
nat-decode (suc m) (suc n) x = ap suc (nat-decode m n x)

nat-decode-encode-id : (m n : ℕ) → nat-encode m n o nat-decode m n ~ id
nat-decode-encode-id zero zero tt = refl
nat-decode-encode-id (suc m) (suc n) c = (tr-Pf (λ x → nat-code (suc m) x) suc (nat-decode m n c) (nat-r m)) ^ ∘ nat-decode-encode-id m n c


nat-encode-decode-id : (m n : ℕ) → nat-decode m n o nat-encode m n ~ id
nat-encode-decode-id zero .zero refl = refl
nat-encode-decode-id (suc m) .(suc m) refl = ap (ap suc ) (nat-encode-decode-id m m refl)

thm2-13-1 : (m n : ℕ) → (m ≡ n) ≃ nat-code m n
thm2-13-1 m n = equiv-adjointify (nat-encode m n , (nat-decode m n) ,
                                 nat-decode-encode-id m n , nat-encode-decode-id m n)


{- paths in a coproduct -}

coprod-code : {i j : Level} {A : Type i} {B : Type j}
              (a₀ : A)
              → A + B → Type (i ⊔ j)
coprod-code {i} {j} a₀ (inl a) = raise j (a₀ ≡ a)
coprod-code {i} {j} a₀ (inr b) = raise _ Empty

coprod-encode : {i j : Level} {A : Type i} {B : Type j}
                (a₀ : A)
                → (x : A + B) (p : inl a₀ ≡ x) → coprod-code a₀ x
coprod-encode a₀ x p = transport (coprod-code a₀) p (map-raise refl)

coprod-decode : {i j : Level} {A : Type i} {B : Type j}
                (a₀ : A)
                → (x : A + B) (c : coprod-code a₀ x) → (inl a₀ ≡ x)
coprod-decode a₀ (inl x) c = ap inl (map-inv-raise c)
coprod-decode a₀ (inr x) (map-raise ())

coprod-encode-decode-id : {i j : Level} {A : Type i} {B : Type j}
                          (a₀ : A)
                          → (x : A + B) → coprod-encode a₀ x o coprod-decode a₀ x ~ id
coprod-encode-decode-id a₀ (inl a) = λ { (map-raise refl) → refl}
coprod-encode-decode-id a₀ (inr b) = λ { (map-raise ())}

coprod-decode-encode-id : {i j : Level} {A : Type i} {B : Type j}
                          (a₀ : A)
                          → (x : A + B) → coprod-decode a₀ x o coprod-encode a₀ x ~ id
coprod-decode-encode-id a₀ (inl a) = λ { refl → refl}
coprod-decode-encode-id a₀ (inr b) = λ { ()}


thm2-12-5 : {i j : Level} {A : Type i} {B : Type j}
            (a₀ : A)
            → (x : A + B) → (inl a₀ ≡ x) ≃ coprod-code a₀ x
thm2-12-5 a₀ x = equiv-adjointify (coprod-encode a₀ x , coprod-decode a₀ x , coprod-encode-decode-id a₀ x , coprod-decode-encode-id a₀ x)

-- Bool is Unit + Unit

Bool-is-coprod : Bool ≃ (Unit + Unit)
Bool-is-coprod = equiv-adjointify ((λ { true → inl tt ; false → inr tt}) ,
                                  (λ { (inl x) → true ; (inr x) → false}) ,
                                  (λ { (inl tt) → refl ; (inr tt) → refl}) ,
                                  λ { true → refl ; false → refl})

foo₁ : {i : Level} {A : Type i} {x y z : A} (p : x ≡ y) (q : y ≡ z) (s : x ≡ z)
       → p ≡ s ∘ q ^ → p ∘ q ≡ s
foo₁ refl refl s x = x ∘ p-refl s


lemma₁ : {i j : Level} {A : Type i} {B : Type j} (f : A → B) (g : B → A) (α : f o g ~ id) (a a' : A) (p : a ≡ a')
         → ap f p ≡ ((whisker-r α f a ^) ∘ (ap f (ap (g o f) p))) ∘ whisker-r α f a'
lemma₁ f g α a .a refl = p=qr^-to-pr=q (whisker-r α f a ^ ∘ refl) refl (whisker-r α f a) (p-refl (α (f a) ^)) ^

lemma₂ : {i j : Level} {A : Type i} {B : Type j} (f : A → B) (g : B → A) (β : g o f ~ id) (a a' : A) (p : a ≡ a')
         → ap (g o f) p ≡ β a ∘ p ∘ β a' ^
lemma₂ f g β a .a refl = pp^ (β a) ^

lemma₄ : {i j : Level} {A : Type i} {B : Type j} (f : A → B) (g : B → A) (α : f o g ~ id) (β : g o f ~ id) (a a' : A) (p : a ≡ a')
         → ((whisker-r α f a ^) ∘ (ap f (ap (g o f) p))) ∘ whisker-r α f a' ≡ ((whisker-r α f a ^) ∘ (ap f (β a ∘ p ∘ β a' ^))) ∘ whisker-r α f a'
lemma₄ f g α β a .a refl = p=q-to-pr=qr (p=q-to-rp=rq (transport (λ t → refl ≡ ap f (t)) ((pp^ (β a)) ^) refl) (α (f a) ^) ) (whisker-r α f a)


lemma₅a : {i : Level} {A : Type i} {x y z w : A}
          → (p : x ≡ y) (r : x ≡ z) (s : z ≡ w)
          → p ∘ (p ^ ∘ r ∘ s) ∘ s ^ ≡ r
lemma₅a refl refl refl = refl


lemma₅ : {i j : Level} {A : Type i} {B : Type j} (f : A → B) (g : B → A) (α : f o g ~ id) (β : g o f ~ id) (a a' : A) (p' : g (f a) ≡ g (f a'))
       → ((whisker-r α f a ^) ∘ (ap f (β a ∘ (β a ^ ∘ p' ∘ β a') ∘ β a' ^))) ∘ whisker-r α f a' ≡ ((whisker-r α f a ^) ∘ ap f p') ∘ (whisker-r α f a')
lemma₅ f g α β a a' p' = p=q-to-pr=qr (p=q-to-rp=rq (ap (λ p → ap f p) (lemma₅a (β a) p' (β a'))) (α (f a) ^)) (whisker-r α f a')

lemma₆ : {i j : Level} {A : Type i} {B : Type j} (f : A → B) (g : B → A) (α : f o g ~ id) (a a' : A) (q : f a ≡ f a')
       → ((whisker-r α f a ^) ∘ ap f (ap g q)) ∘ (whisker-r α f a') ≡ q
lemma₆ f g α a a' q = (ass-l (whisker-r α f a ^) (ap f (ap g q)) (whisker-r α f a') ∘ p=qr-to-q^p=r (ap f (ap g q) ∘ whisker-r α f a') (ap id q) (whisker-r α f a) (ap (λ p → p ∘ whisker-r α f a') ((ap-gf f g q) ^) ∘ (homotopy-natural α q ) ^)) ∘ ap-id q
{- paths in identity types -}

thm2-11-1-inv : {i j : Level} {A : Type i} {B : Type j} (f : A → B) (g : B → A) (α : f o g ~ id) (β : g o f ~ id) (a a' : A)
                → f a ≡ f a' → a ≡ a'
thm2-11-1-inv f g α β a a' X = (β a) ^ ∘ ap g X ∘ β a'


thm2-11-1-τ : {i j : Level} {A : Type i} {B : Type j} (f : A → B) (g : B → A) (α : f o g ~ id) (β : g o f ~ id) (a a' : A) (q : f a ≡ f a')
              → ap f (β a ^ ∘ ap g q ∘ β a') ≡ q
thm2-11-1-τ f g α β a a' q = lemma₁ f g α a a' (β a ^ ∘ ap g q ∘ β a') ∘
            lemma₄ f g α β a a' (β a ^ ∘ ap g q ∘ β a') ∘
            lemma₅ f g α β a a' (ap g q) ∘
            lemma₆ f g α a a' q

thm2-11-1-ε : {i j : Level} {A : Type i} {B : Type j} (f : A → B) (g : B → A) (β : g o f ~ id) (a a' : A) (p : a ≡ a')
              → β a ^ ∘ ap g (ap f p) ∘ β a' ≡ p
thm2-11-1-ε f g β a .a refl = p^p (β a)

thm2-11-1 : {i j : Level} {A : Type i} {B : Type j} {f : A → B} {a a' : A}
            → isEquiv f
            → isEquiv (λ (p : a ≡ a') → ap f p)
thm2-11-1 {i} {j} {A} {B} {f} {a} {a'} X = let g = pr₁ X
                                               β = pr₁ (pr₂ X)
                                               α = pr₁ (pr₃ X)
                                            in isequiv-adjointify (thm2-11-1-inv f g α β a a' ,
                                              thm2-11-1-τ f g α β a a' ,
                                              thm2-11-1-ε f g β a a')


lemma2-11-2i : {i : Level} {A : Type i} {x₁ x₂ : A}
               (a : A) (p : x₁ ≡ x₂) (q : a ≡ x₁)
               → transport (λ x → a ≡ x) p q ≡ q ∘ p
lemma2-11-2i a refl q = p-refl q ^

lemma2-11-2ii : {i : Level} {A : Type i} {x₁ x₂ : A}
                (a : A) (p : x₁ ≡ x₂) (q : x₁ ≡ a)
               → transport (λ x → x ≡ a) p q ≡ p ^ ∘ q
lemma2-11-2ii a refl q = refl

lemma2-11-2iii : {i : Level} {A : Type i} {x₁ x₂ : A}
                 (a : A) (p : x₁ ≡ x₂) (q : x₁ ≡ x₁)
                 → transport (λ x → x ≡ x) p q ≡ p ^ ∘ q ∘ p
lemma2-11-2iii a refl q = p-refl q ^

thm2-11-3 : {i j : Level} {A : Type i} {B : Type j} {a a' : A}
            → (f g : A → B) (p : a ≡ a') (q : f a ≡ g a)
            → transport (λ x → f x ≡ g x) p q ≡ (ap f p) ^ ∘ q ∘ ap g p
thm2-11-3 f g refl q = p-refl q ^

thm2-11-4 : {i j : Level} {A : Type i} {B : A → Type j} {a a' : A}
            (f g : (x : A) → B x) (p : a ≡ a') (q : f a ≡ g a)
            → transport (λ x → f x ≡ g x) p q ≡ (apD f p) ^ ∘ ap (transport B p) q ∘ apD g p
thm2-11-4 f g refl q = ap-id q ^ ∘ (p-refl (ap id q) ^)

thm2-11-5 : {i : Level} {A : Type i} {a a' : A}
            (p : a ≡ a') (q : a ≡ a) (r : a' ≡ a')
            → (transport (λ x → (x ≡ x)) p q ≡ r) ≃ (q ∘ p ≡ p ∘ r)
thm2-11-5 refl q r = equiv-adjointify ((λ { x → p-refl q ∘ x}) , (λ { x → p-refl q ^ ∘ x}) ,
  (λ { refl → prefl-o-prefl^ {_} {_} {_} {q}}) , λ {refl → prefl^-o-prefl {_} {_} {_} {q}})
