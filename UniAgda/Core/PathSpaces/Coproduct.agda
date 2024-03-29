{-# OPTIONS --without-K --safe --no-import-sorts #-}
module UniAgda.Core.PathSpaces.Coproduct where

open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Functions
open import UniAgda.Core.Types.Identity
open import UniAgda.Core.Types.Sigma
open import UniAgda.Core.Types.Coproduct
open import UniAgda.Core.Types.Empty
open import UniAgda.Core.Types.Unit
open import UniAgda.Core.Types.Bool

open import UniAgda.Core.PathAlgebra
open import UniAgda.Core.Homotopy
open import UniAgda.Core.Equivalences

-- * Paths in Coproducts

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



coprod-code' : {i j : Level} {A : Type i} {B : Type j}
              (b₀ : B)
              → A + B → Type (i ⊔ j)
coprod-code' {i} {j} b₀ (inl a) = raise _ Empty
coprod-code' {i} {j} b₀ (inr b) = raise i (b₀ ≡ b)

coprod-encode' : {i j : Level} {A : Type i}  {B : Type j}
                (b₀ : B)
                → (x : A + B) (p : inr b₀ ≡ x) → coprod-code' b₀ x
coprod-encode' b₀ x p = transport (coprod-code' b₀) p (map-raise refl)

coprod-decode' : {i j : Level} {A : Type i} {B : Type j}
                (b₀ : B)
                → (x : A + B) (c : coprod-code' b₀ x) → (inr b₀ ≡ x)
coprod-decode' b₀ (inl x) (map-raise ())
coprod-decode' b₀ (inr x) c = ap inr (map-inv-raise c) 

coprod-encode-decode-id' : {i j : Level} {A : Type i} {B : Type j}
                           (b₀ : B)
                          → (x : A + B) → coprod-encode' b₀ x o coprod-decode' b₀ x ~ id
coprod-encode-decode-id' b₀ (inl a) = λ { (map-raise ())}
coprod-encode-decode-id' b₀ (inr b) = λ { (map-raise refl) → refl} 

coprod-decode-encode-id' : {i j : Level} {A : Type i} {B : Type j}
                          (b₀ : B)
                          → (x : A + B) → coprod-decode' b₀ x o coprod-encode' b₀ x ~ id
coprod-decode-encode-id' b₀ (inl a) = λ {()}
coprod-decode-encode-id' b₀ (inr b) = λ {refl → refl}


thm2-12-5ii : {i j : Level} {A : Type i} {B : Type j}
              (b₀ : B)
              → (x : A + B) → (inr b₀ ≡ x) ≃ coprod-code' b₀ x
thm2-12-5ii b₀ x = equiv-adjointify (coprod-encode' b₀ x , coprod-decode' b₀ x , coprod-encode-decode-id' b₀ x , coprod-decode-encode-id' b₀ x)

-- * Bool is a coproduct

Bool-is-coprod : Bool ≃ (Unit + Unit)
Bool-is-coprod = equiv-adjointify ((λ { true → inl tt ; false → inr tt}) ,
                                  (λ { (inl x) → true ; (inr x) → false}) ,
                                  (λ { (inl tt) → refl ; (inr tt) → refl}) ,
                                  λ { true → refl ; false → refl})
