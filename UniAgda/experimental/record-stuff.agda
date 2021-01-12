{-# OPTIONS --without-K #-}
module UniAgda.experimental.record-stuff where

open import UniAgda.everything public
record magma {i : Level} : Type (lsuc i) where
  field
    carrier : Type i
    op : carrier → carrier → carrier

open magma
magma-sig : ∀ {i}
            → Type (lsuc i)
magma-sig {i} =
  Σ[ carrier ∈ (Type i) ] (
    carrier → carrier → carrier)

carrier' : ∀ {i}
           (M : magma-sig {i})
           → Type i
carrier' M =
  pr₁ M

op' : ∀ {i}
      (M : magma-sig {i})
      → (pr₁ M → pr₁ M → pr₁ M)
op' M =
  pr₂ M


magma-rec→sig : ∀ {i}
                (M : magma {i})
                → magma-sig {i}
magma-rec→sig M =
  carrier M ,
  op M

magma-sig→rec : ∀ {i}
                (M : magma-sig {i})
                → magma {i}
carrier (magma-sig→rec {i} M) = carrier' M
op (magma-sig→rec {i} M) = op' M

magma-η : ∀ {i}
          (M : magma {i})
          → (magma-sig→rec o magma-rec→sig) M ≡ M
magma-η {i} M = {!!}


