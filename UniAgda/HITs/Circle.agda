{-# OPTIONS --without-K --rewriting --no-import-sorts #-}
module UniAgda.HITs.Circle where

open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Identity
open import UniAgda.HITs.Core

postulate
  S¹ : Type lzero
  base : S¹
  loop : base ≡ base

postulate
  S¹-rec : {i : Level} {B : Type i} (b : B) (s : b ≡ b)
          → S¹ → B

  βS¹-rec-base : {i : Level} {B : Type i} (b : B) (s : b ≡ b)
          → S¹-rec b s base ↦ b

{-# REWRITE βS¹-rec-base #-}

postulate
  βS¹-rec-loop : {i : Level} {B : Type i} (b : B) (s : b ≡ b)
          → ap (λ x → S¹-rec b s x) loop ≡ s

postulate
  S¹-ind : {i : Level} {P : S¹ → Type i} (b : P base) (s : transport P loop b ≡ b)
          → (x : S¹) → P x

  βS¹-ind-base : {i : Level} {P : S¹ → Type i} (b : P base) (s : transport P loop b ≡ b)
             → S¹-ind b s base ↦ b

{-# REWRITE βS¹-ind-base #-}

postulate
  βS¹-ind-loop : {i : Level} {P : S¹ → Type i} (b : P base) (s : transport P loop b ≡ b)
             → apD (λ x → S¹-ind b s x) loop ≡ s
