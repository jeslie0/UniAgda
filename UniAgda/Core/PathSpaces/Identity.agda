{-# OPTIONS --without-K --no-import-sorts #-}
module UniAgda.Core.PathSpaces.Identity where


open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Functions
open import UniAgda.Core.Types.Identity
open import UniAgda.Core.Types.Sigma

open import UniAgda.Core.PathAlgebra
open import UniAgda.Core.Homotopy
open import UniAgda.Core.Equivalences

open import UniAgda.Core.PathSpaces.Sigma
open import UniAgda.Core.Axioms

-- * Paths in Identity Types

private
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
thm2-11-1 {i} {j} {A} {B} {f} {a} {a'} X =
  let g = pr₁ X
      β = pr₁ (pr₂ X)
      α = pr₁ (pr₂ (pr₂ X))
  in
  isequiv-adjointify
    (thm2-11-1-inv f g α β a a' ,
    thm2-11-1-τ f g α β a a' ,
    thm2-11-1-ε f g β a a')

-- * Other results

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



Sigma-path-paths : ∀ {i₁ i₂}{A : Type i₁} {B : A → Type i₂}
                   {X Y : Σ A B}
                   {p q : X ≡ Y}
                   → (p ≡ q) ≃ (Σ[ s ∈ pr₁ (path-sigma p) ≡ pr₁ (path-sigma q) ] transport (λ v →  transport B v (pr₂ X) ≡ pr₂ Y) s (pr₂ (path-sigma p)) ≡ (pr₂ (path-sigma q)))
Sigma-path-paths = (ap path-sigma , thm2-11-1 (pr₂ (thm2-7-2))) oₑ  thm2-7-2


Pi-path-paths : ∀ {i₁ i₂} {A : Type i₁} {B : A → Type i₂}
                {f g : (a : A) → B a}
                {p q : f ≡ g}
                → (p ≡ q) ≃ (happlyD p ~ happlyD q)
Pi-path-paths = ((ap happlyD) , thm2-11-1 (pr₂ (funextD-equiv))) oₑ funextD-equiv

Pi-path-paths-implicit : ∀ {i₁ i₂} {A : Type i₁} {B : A → Type i₂}
                {f g : {a : A} → B a}
                {p q : (λ {a} → f {a}) ≡ (λ {a} → g {a})}
                → (p ≡ q) ≃ (implicit-happly p ~ implicit-happly q)
Pi-path-paths-implicit = ((ap implicit-happly) , thm2-11-1 (pr₂ (implicit-funext-equiv ^ᵉ))) oₑ
  equiv-adjointify
    ((λ P x → happlyD P x ) ,
    (λ Q → funextD λ x → Q x) ,
    (λ Q → happlyD-funextD~Id λ x → Q x) ,
    λ P → funextD-happlyD~Id P)




ap-of-equiv : ∀ {i₁ i₂} {A : Type i₁} {B : Type i₂} {x y : A}
              (p q : x ≡ y)
              (f : A → B)
              → isEquiv f
              → ap f p ≡ ap f q
              → p ≡ q
ap-of-equiv {x = x} {y = y} p q f X P =
    equiv-types-eq
      (((ap f) , (thm2-11-1 {a = x} {a' = y} X)) ^ᵉ)
      P
