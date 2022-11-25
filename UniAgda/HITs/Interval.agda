{-# OPTIONS --without-K --rewriting --no-import-sorts #-}
module UniAgda.HITs.Interval where

open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Identity
open import UniAgda.HITs.Core 

postulate
  I : Type lzero
  i0 : I
  i1 : I
  seg : i0 ≡ i1

postulate
  I-rec : {i : Level} {C : Type i} (a b : C) (p : a ≡ b)
          → I → C
  βi0 : {i : Level} {C : Type i} (a b : C) (p : a ≡ b) →
         I-rec a b p i0 ↦ a
  βi1 : {i : Level} {C : Type i} (a b : C) (p : a ≡ b) →
         I-rec a b p i1 ↦ b
{-# REWRITE βi0 #-}
{-# REWRITE βi1 #-}

postulate
  βseg : {i : Level} {C : Type i}
         (a b : C) (p : a ≡ b)
         → ap (λ i → I-rec a b p i) seg ≡ p

postulate
  I-ind : {i : Level} → {P : I → Type i} → (a : P i0) (b : P i1) → (s : transport P seg a ≡ b)
         → (x : I) → P x

  βI-ind-i0 : {i : Level} → {P : I → Type i} → (a : P i0) (b : P i1) → (s : transport P seg a ≡ b)
           → I-ind a b s i0 ↦ a

  βI-ind-i1 : {i : Level} → {P : I → Type i} → (a : P i0) (b : P i1) → (s : transport P seg a ≡ b)
           → I-ind a b s i1 ↦ b

{-# REWRITE βI-ind-i0 #-}
{-# REWRITE βI-ind-i1 #-}

postulate
  βI-ind-seg : {i : Level} (P : I → Type i) → (a : P i0) (b : P i1) → (s : transport P seg a ≡ b)
          → apD (λ i → I-ind a b s i) seg ≡ s
