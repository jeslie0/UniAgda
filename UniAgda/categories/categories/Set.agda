{-# OPTIONS --without-K #-}
module UniAgda.categories.categories.Set where

open import UniAgda.categories.category public

{- Set is a precategory -}
SET : ∀ {i} → Precategory {_} {_}
SET {i} =
  (Set_ i) ,
  (λ a b → pr₁ a → pr₁ b) ,
  (λ a b → func-of-sets-is-set (pr₂ b)) ,
  id ,
  _o_ ,
  (λ f → refl) ,
  (λ f → refl) ,
  λ f g h → refl
-- ob (SET {i}) = Set_ i
-- hom (SET {i}) a b = (pr₁ a) → (pr₁ b)
-- hom-set (SET {i}) a b = func-of-sets-is-set (pr₂ b)
-- Id (SET {i}) = id
-- comp (SET {i}) = _o_
-- l-Id (SET {i}) f = refl
-- r-Id (SET {i}) f = refl
-- ass (SET {i}) f g h = refl


{- We show that Set is a (univalent) category -}

-- id-equiv-to-prop-on-type : ∀ {i j} (X X' : Type i) (Q : Type i → Type j)
--               (F : (A : Type i) → isProp (Q A))
--               → (a : Q X) → (b : Q X')
--               → (X ≡ X') ≃ ((X , a) ≡ (X' , b))
-- id-equiv-to-prop-on-type X X' Q F a b = equiv-adjointify ((λ { refl → refl , (F X a b)}) ,
--                          (λ { (p , u) → p}) ,
--                          (λ { (refl , refl) → path-equiv-sigma (refl , (props-are-sets (F X) _ _ _ _))}) ,
--                          λ { refl → refl}) oₑ (thm2-7-2 ^ᵉ)


UA-for-sets : ∀ {i} (X X' : Set_ i)
              → (X ≡ X') ≃ (pr₁ X ≃ pr₁ X')
UA-for-sets {i} (X₁ , a) (X₂ , b) = ((univalence ^ᵉ) oₑ id-equiv-to-prop-on-type X₁ X₂ isSet (λ A → isSet-is-prop A) a b) ^ᵉ


set-equiv-iso-qinv : ∀ {i} (A B : ob (SET {i})) → (qequiv (pr₁ A) (pr₁ B)) ≃ (iso {_} {_} {SET {i}} A B)
set-equiv-iso-qinv {i} (X , a) (X' , b) = equiv-adjointify ((λ { (f , g , α , β) → f , (g , ((funext α) , (funext β)))}) ,
                   ((λ { (f , g , α , β) → f , (g , ((happly α) , (happly β)))}) ,
                   ((λ { (f , g , α , β) → path-equiv-sigma (refl ,
                     transport (λ F → (g , funext (happly α) , F) ≡ (g , α , β)) (pr₁ (pr₂ happly-isEquiv) β ^)
                     (transport (λ F → (g , F , id β) ≡ (g , α , β)) (pr₁ (pr₂ happly-isEquiv) α ^) refl))}) ,
                   λ { (f , g , α , β) → path-equiv-sigma (refl , (transport (λ F → (g , happly (funext α) , F) ≡ (g , α , β)) (pr₁ (pr₂ (pr₂ happly-isEquiv)) β ^)
                     (transport (λ F → (g , F , id β) ≡ (g , α , β)) (pr₁ (pr₂ (pr₂ happly-isEquiv)) α ^) refl)))})))



qinv-of-sets-is-prop : ∀ {i} {A B : Set_ i} (f : pr₁ A → pr₁ B)
                       → isProp (qinv f)
qinv-of-sets-is-prop {i} {X , a} {Y , b} f (g , α , β) (g' , α' , β') = path-equiv-sigma ((funext (λ y → β' (g y) ^ ∘ ap g' (α y))) ,
                     path-equiv-sigma ((funextD (λ y → b _ _ _ _)) , funextD λ x → a _ _ _ _))

SET-id-equiv-iso : ∀ {i} (A B : ob (SET {i})) → (A ≡ B) ≃ (iso {_} {_} {SET {i}} A B)
SET-id-equiv-iso {i} (X , a) (X' , b) = UA-for-sets (X , a) (X' , b) oₑ (equiv-fibres-to-equiv-sigma (λ f → props-equiv (isEquiv-is-prop f) (qinv-of-sets-is-prop {i} {X , a} {X' , b} f) isEquiv-to-qinv qinv-to-ishae) oₑ (set-equiv-iso-qinv (X , a) (X' , b)))

id-to-iso-equality : ∀ {i} (A B : ob (SET {i}))
           → pr₁ (SET-id-equiv-iso A B) ≡ id-to-iso (SET {i}) {A} {B}
id-to-iso-equality {i} (X , a) (X' , b) = funext λ { refl → path-equiv-sigma ((funext (λ x → refl)) ,
         isIso-is-prop {_} {_} {SET {i}} {(X , a)} {(X' , b)} _ _ _)}

SET-is-category : ∀ {i} → isCategory (SET {i})
SET-is-category A B =  transport (λ f → isEquiv f) (id-to-iso-equality A B) (pr₂ (SET-id-equiv-iso A B))
