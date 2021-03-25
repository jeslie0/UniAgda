{-# OPTIONS --without-K --rewriting #-}
module UniAgda.experimental.exp5 where
open import UniAgda.Core.Everything

private
  variable
    i j k : Level










open import UniAgda.HITs.PropTrunc

isFinite : ∀ {i}
           (A : Type i)
           → Type i
isFinite A = ∥ (Σ[ n ∈ ℕ ] (A ≃ Fin n)) ∥

Fin-set : ∀ (i)
          → Type (lsuc i)
Fin-set i = Σ[ A ∈ (Type i) ] isFinite A

finite-sets-are-sets : (A : Fin-set i)
                       → isSet (pr₁ A)
finite-sets-are-sets (A , X) =
  Ptrunc-rec
    (isSet-is-prop A)
    (λ { (n , f) → equiv-with-set (f ^ᵉ) (Fin-n-is-set n)})
    X



-- foo : (A : Type i) (B : Type j) (X : isFinite A) (Y : isFinite B)
--       → isSet (A → B)
-- foo A B X Y = func-of-sets-is-set (Finite-sets-are-sets )






