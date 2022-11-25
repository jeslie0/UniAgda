
{-# OPTIONS --without-K --no-import-sorts #-}
module UniAgda.Equiv.Bool where

open import UniAgda.Core.Types.Universes
open import UniAgda.Core.Types.Functions
open import UniAgda.Core.Types.Identity
open import UniAgda.Core.Types.Sigma
open import UniAgda.Core.Types.Bool
open import UniAgda.Core.Types.Coproduct
open import UniAgda.Core.Types.Empty
open import UniAgda.Core.Types.Unit

open import UniAgda.Core.Homotopy
open import UniAgda.Core.Equivalences
open import UniAgda.Core.Axioms

open import UniAgda.Core.SetsAndLogic.ContrPropSet1Type
open import UniAgda.Core.SetsAndLogic.Props
open import UniAgda.Core.SetsAndLogic.Equivalences

open import UniAgda.Core.PathSpaces.Sigma


-- * Bool is equivalent to (equiv Bool Bool)
-- We first need to define functions each way.

private
  f : Bool ≃ Bool → Bool
  f (h , X) = h true

  g : Bool → Bool ≃ Bool
  g true = equiv-adjointify (id , id , hrefl , hrefl)
  g false = equiv-adjointify (swap , swap ,
                                   (λ { true → refl
                                      ; false → refl}) ,
                                   λ { true → refl
                                     ; false → refl})


-- Now we need the required homotopies. The first is easy.


private
  η : f o g ~ id
  η true = refl
  η false = refl


-- For the second, we need the to use three important results
-- regarding Bool. The first is that every \(x\) in Bool is equal to
-- true or false.

eq-T-F-Bool : (x : Bool) → (x ≡ true) + (x ≡ false)
eq-T-F-Bool true = inl refl 
eq-T-F-Bool false = inr refl 


-- Next, we show that true cannot equal false.

true-neq-false : ¬ (true ≡ false)
true-neq-false p = transport (λ { true → Unit ; false → Empty}) p tt


-- Finally, we need that every equivalence on Bool commutes with
-- \(\text{swap}\). That is, if \(f: \text{Bool} \to \text{Bool}\) is
-- an equivalence, then \(\text{swap} \circ f = f \circ
-- \text{swap}\). This is just done by a case analysis on both
-- \(h(true), h(false)\) being true or false.

Bool-autoequiv-not-const : (H : Bool ≃ Bool) → (pr₁ H o swap ~ swap o pr₁ H)
Bool-autoequiv-not-const (h , h' , α , β , γ) with (eq-T-F-Bool (h true)) | eq-T-F-Bool (h false)
... | inl q | inl s = λ {x → Empty-ind (true-neq-false (α true ^ ∘ ap h' (q ∘ s ^) ∘ α false))}
... | inl q | inr s = λ { true → s ∘ ap swap q ^
                        ; false → q ∘ ap swap s ^}
... | inr q | inl s = λ { true → s ∘ ap swap q ^
                        ; false → q ∘ ap swap s ^}
... | inr q | inr s = λ {x → Empty-ind (true-neq-false (α true ^ ∘ ap h' (q ∘ s ^) ∘ α false))}


-- We are now ready to give the final homotopy.

private
  ϵ : g o f ~ id
  ϵ (h , h' , α , β , γ) with eq-T-F-Bool (h true) | eq-T-F-Bool (h false)
  ... | inl q | inl s = fibres-props-eq
                        isEquiv-is-prop _ _
                        (funext λ { x → Empty-ind $ true-neq-false
                          (α true ^ ∘ ap h' (q ∘ s ^) ∘ α false)})
  ... | inl q | inr s = fibres-props-eq
                        isEquiv-is-prop _ _
                        (funext λ { true → ap (λ Z → pr₁ (g Z) true) q ∘ q ^
                                  ; false → ap (λ Z → pr₁ (g Z) false) q ∘ s ^})
  ... | inr q | inl s = fibres-props-eq
                        isEquiv-is-prop _ _
                        (funext λ { true → ap (λ Z → pr₁ (g Z) true) q ∘ q ^
                                  ; false → ap (λ Z → pr₁ (g Z) false) q ∘ s ^})
  ... | inr q | inr s = fibres-props-eq
                        isEquiv-is-prop _ _
                        (funext λ { x → Empty-ind $ true-neq-false
                          (α true ^ ∘ ap h' (q ∘ s ^) ∘ α false)})


-- We can now prove the desired result.
--  Exercise2.13

2≃2-equiv-2 : (Bool ≃ Bool) ≃ Bool
2≃2-equiv-2 = equiv-adjointify (f , g , η , ϵ)
