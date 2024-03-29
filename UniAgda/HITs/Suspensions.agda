{-# OPTIONS --without-K --rewriting --no-import-sorts #-}
module UniAgda.HITs.Suspensions where


open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Functions
open import UniAgda.Core.Types.Identity
open import UniAgda.Core.Types.Sigma
open import UniAgda.Core.Types.Nat
open import UniAgda.Core.Types.Bool

open import UniAgda.Core.Homotopy
open import UniAgda.Core.Equivalences

open import UniAgda.Core.PathAlgebra
open import UniAgda.Core.PathSpaces.Identity
open import UniAgda.HITs.Core
open import UniAgda.HITs.Circle

postulate
  Susp : {i : Level} (A : Type i) → Type i
  N : {i : Level} {A : Type i} → Susp A
  S : {i : Level} {A : Type i} → Susp A
  merid : {i : Level} {A : Type i}
          → A → N {i} {A} ≡ S {i} {A}

  Susp-rec : {i j : Level} {A : Type i} {B : Type j}
             → (n s : B) → (m : A → n ≡ s)
             → Susp A → B

  βSusp-recN : {i j : Level} {A : Type i} {B : Type j}
              → (n s : B) → (m : A → n ≡ s)
              → Susp-rec n s m N ↦ n

  βSusp-recS : {i j : Level} {A : Type i} {B : Type j}
              → (n s : B) → (m : A → n ≡ s)
              → Susp-rec n s m S ↦ s

{-# REWRITE βSusp-recN #-}
{-# REWRITE βSusp-recS #-}

postulate
  βSusp-rec-merid : {i j : Level} {A : Type i} {B : Type j}
                    → (n s : B) → (m : A → n ≡ s) → (a : A)
                    → ap (Susp-rec n s m) (merid a) ≡ m a

postulate
  Susp-ind : {i j : Level} {A : Type i} {P : Susp A → Type j}
             (n : P N) (s : P S) (m : (a : A) → transport P (merid a) n ≡ s)
             → (x : Susp A) → P x

  βSusp-ind-N : {i j : Level} {A : Type i} {P : Susp A → Type j}
                (n : P N) (s : P S) (m : (a : A) → transport P (merid a) n ≡ s)
                → Susp-ind n s m N ↦ n

  βSusp-ind-S : {i j : Level} {A : Type i} {P : Susp A → Type j}
                (n : P N) (s : P S) (m : (a : A) → transport P (merid a) n ≡ s)
                → Susp-ind n s m S ↦ s

{-# REWRITE βSusp-ind-N #-}
{-# REWRITE βSusp-ind-S #-}

postulate
  βSusp-ind-merid : {i j : Level} {A : Type i} {P : Susp A → Type j}
                    (n : P N) (s : P S) (m : (a : A) → transport P (merid a) n ≡ s) (a : A)
                    → apD (Susp-ind n s m) (merid a) ↦  m a

{-# REWRITE βSusp-ind-merid #-}

𝕊 : ℕ → Type lzero
𝕊 zero = Bool
𝕊 (suc zero) = S¹
𝕊 (suc (suc n)) = Susp (𝕊 (suc n))



{- Properties -}

S¹-to-Susp-Bool : S¹ → Susp Bool
S¹-to-Susp-Bool =  S¹-rec {_} {Susp Bool} N (merid (false) ∘ merid (true) ^)

private
  m₁ : Bool → base ≡ base
  m₁ true = refl
  m₁ false = loop

Susp-Bool-to-S¹ : Susp Bool → S¹
Susp-Bool-to-S¹ = Susp-rec {_} {_} {Bool} {S¹} base base m₁

private
  Susp-Bool-eqv-S¹-hom₁-lemma₁ : ap Susp-Bool-to-S¹ (merid false) ≡ loop
  Susp-Bool-eqv-S¹-hom₁-lemma₁ = βSusp-rec-merid {_} {_} {Bool} {S¹} base base m₁ false

  Susp-Bool-eqv-S¹-hom₁-lemma₂ : ap S¹-to-Susp-Bool loop ≡ merid false ∘ merid true ^
  Susp-Bool-eqv-S¹-hom₁-lemma₂ = βS¹-rec-loop {_} {Susp Bool} N (merid false ∘ merid true ^)

  Susp-Bool-eqv-S¹-hom₁-lemma₃ : ap Susp-Bool-to-S¹ (merid true) ≡ refl
  Susp-Bool-eqv-S¹-hom₁-lemma₃ = βSusp-rec-merid {_} {_} {Bool} {S¹} base base m₁ true


Susp-Bool-eqv-S¹-hom₁ : S¹-to-Susp-Bool o Susp-Bool-to-S¹ ~ id
Susp-Bool-eqv-S¹-hom₁ x =
  let g = S¹-to-Susp-Bool
      f = Susp-Bool-to-S¹
  in Susp-ind {_} {_} {Bool} {λ x → (S¹-to-Susp-Bool o Susp-Bool-to-S¹) x ≡ id x} refl
  (merid true)
  (λ { true → thm2-11-3 (g o f) id (merid true) refl ∘
    ap (λ p → p ^ ∘ (ap id (merid true))) (ap-gf g f (merid true)) ∘
    (transport (λ p → ap g p ^ ∘ ap id (merid true) ≡ merid true) (Susp-Bool-eqv-S¹-hom₁-lemma₃ ^))
    (ap-id (merid true))  ;
  false →  thm2-11-3 (g o f) (id) (merid false) refl ∘
    ap (λ p → p ^ ∘ ap id (merid false)) (ap-gf g f (merid false)) ∘
    transport (λ p → ap S¹-to-Susp-Bool (p) ^ ∘ ap id (merid false) ≡ merid true) (Susp-Bool-eqv-S¹-hom₁-lemma₁ ^)
    (transport (λ p → p ^ ∘ ap id (merid false) ≡ merid true) (Susp-Bool-eqv-S¹-hom₁-lemma₂ ^)
    ( ap (λ p → p ∘ ap id (merid false)) (pq-^-to-q^p^ (merid false) (merid true ^)) ∘
    ass-l (merid true ^ ^) (merid false ^) (ap id (merid false)) ∘ p^^q-to-pq (merid true) (merid false ^ ∘ ap id (merid false)) ∘ ap (λ p → merid true ∘ p) (p^-apIDp-to-refl (merid false)) ∘ p-refl (merid true))) }) x

private
  Susp-Bool-eqv-S¹-hom₂-lemma₁ : ap S¹-to-Susp-Bool loop ≡ merid false ∘ merid true ^
  Susp-Bool-eqv-S¹-hom₂-lemma₁ = βS¹-rec-loop N (merid false ∘ merid true ^)


Susp-Bool-eqv-S¹-hom₂ : Susp-Bool-to-S¹ o S¹-to-Susp-Bool ~ id
Susp-Bool-eqv-S¹-hom₂ x =
  let g = S¹-to-Susp-Bool
      f = Susp-Bool-to-S¹
  in  S¹-ind {_} {λ x → (Susp-Bool-to-S¹ o S¹-to-Susp-Bool) x ≡ id x} refl
    (thm2-11-3 (f o g) id loop refl ∘ transport (λ p → p ^ ∘ ap id loop ≡ refl) (ap-gf f g loop ^)
    (transport (λ p → ap Susp-Bool-to-S¹ p ^ ∘ ap id loop ≡ refl) (Susp-Bool-eqv-S¹-hom₂-lemma₁ ^)
    (transport (λ p → p ^ ∘ ap id loop ≡ refl) (apf-pq f (merid false) (merid true ^) ^)
    (transport (λ p → (p ∘ ap Susp-Bool-to-S¹ (merid true ^)) ^ ∘ ap id loop ≡ refl) (Susp-Bool-eqv-S¹-hom₁-lemma₁ ^)
    (transport (λ p → (loop ∘ p) ^ ∘ ap id loop ≡ refl) (apf-p^ f (merid true) ^)
    (transport (λ p → (loop ∘ p ^) ^ ∘ ap id loop ≡ refl) ( Susp-Bool-eqv-S¹-hom₁-lemma₃ ^)
    (transport (λ p → p ^ ∘ ap id loop ≡ refl) (p-refl loop ^)
    (transport (λ p → loop ^ ∘ p ≡ refl) (ap-id loop ^) (p^p loop))))))))) x


Susp-Bool-eqv-S¹ : Susp Bool ≃ S¹
Susp-Bool-eqv-S¹ = equiv-adjointify (Susp-Bool-to-S¹ , (S¹-to-Susp-Bool , Susp-Bool-eqv-S¹-hom₂ , Susp-Bool-eqv-S¹-hom₁))
lemma6-5-1 = Susp-Bool-eqv-S¹
