{-# OPTIONS --without-K --rewriting --no-import-sorts #-}
module UniAgda.HITs.Pushouts where

open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Identity
open import UniAgda.HITs.Core 

postulate
  pushout : {i₁ i₂ i₃ : Level} {A : Type i₁} {B : Type i₂} {C : Type i₃}
            (f : C → A) (g : C → B)
            → Type (i₁ ⊔ i₂ ⊔ i₃)
  left : {i₁ i₂ i₃ : Level} {A : Type i₁} {B : Type i₂} {C : Type i₃}
         (f : C → A) (g : C → B)
         → A → pushout f g

  right : {i₁ i₂ i₃ : Level} {A : Type i₁} {B : Type i₂} {C : Type i₃}
          (f : C → A) (g : C → B)
          → B → pushout f g

  glue : {i₁ i₂ i₃ : Level} {A : Type i₁} {B : Type i₂} {C : Type i₃}
         (f : C → A) (g : C → B)
         → (c : C) → left f g (f c) ≡ right f g (g c)


  pushout-rec : {i₁ i₂ i₃ i₄ : Level} {A : Type i₁} {B : Type i₂} {C : Type i₃} {D : Type i₄}
                { f : C → A } { g : C → B }
                (h₁ : A → D) (h₂ : B → D) → (c : C) → (p : h₁ (f c) ≡ h₂ (g c))
                → pushout f g → D

  βpushout-rec-left : {i₁ i₂ i₃ i₄ : Level} {A : Type i₁} {B : Type i₂} {C : Type i₃} {D : Type i₄}
                      {f : C → A} {g : C → B}
                      (h₁ : A → D) (h₂ : B → D) → (c : C) → (p : h₁ (f c) ≡ h₂ (g c))
                      → pushout-rec h₁ h₂ c p (left f g (f c)) ↦ h₁ (f c)


  βpushout-rec-right : {i₁ i₂ i₃ i₄ : Level} {A : Type i₁} {B : Type i₂} {C : Type i₃} {D : Type i₄}
                       {f : C → A} {g : C → B}
                       (h₁ : A → D) (h₂ : B → D) → (c : C) → (p : h₁ (f c) ≡ h₂ (g c))
                       → pushout-rec h₁ h₂ c p (right f g (g c)) ↦ h₂ (g c)

{-# REWRITE βpushout-rec-left #-}
{-# REWRITE βpushout-rec-right #-}
postulate
  βpushout-rec-glue : {i₁ i₂ i₃ i₄ : Level} {A : Type i₁} {B : Type i₂} {C : Type i₃} {D : Type i₄}
                      {f : C → A} {g : C → B}
                      (h₁ : A → D) (h₂ : B → D) → (c : C) → (p : h₁ (f c) ≡ h₂ (g c))
                      → ap (pushout-rec h₁ h₂ c p) (glue f g c) ≡ p
