{-# OPTIONS --without-K --safe --no-import-sorts #-}
module UniAgda.Core.PathSpaces.Nat where

open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Functions
open import UniAgda.Core.Types.Identity
open import UniAgda.Core.Types.Sigma
open import UniAgda.Core.Types.Nat
open import UniAgda.Core.Types.Unit
open import UniAgda.Core.Types.Empty
open import UniAgda.Core.Types.Coproduct

open import UniAgda.Core.PathAlgebra
open import UniAgda.Core.Homotopy
open import UniAgda.Core.Equivalences

-- * Paths in Nat

nat-code : ℕ → ℕ → Type lzero
nat-code zero zero = Unit
nat-code zero (suc m) = Empty
nat-code (suc n) zero = Empty
nat-code (suc n) (suc m) = nat-code n m

nat-r : (n : ℕ) → nat-code n n
nat-r zero = tt
nat-r (suc n) = nat-r n

nat-encode : (m n : ℕ) → m ≡ n → nat-code m n
nat-encode m n p = transport (nat-code m) p (nat-r m)

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
