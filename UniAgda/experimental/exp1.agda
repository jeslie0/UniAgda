{-# OPTIONS --without-K #-}
module UniAgda.experimental.exp1 where

open import UniAgda.everything public


{- Set is a cat -}
SET : ∀ {i} → Precategory
ob (SET {i}) = Set_ i
hom (SET {i}) a b = (pr₁ a) → (pr₁ b)
hom-set (SET {i}) a b = func-of-sets-is-set (pr₂ b)
Id (SET {i}) = id
comp (SET {i}) = _o_
l-Id (SET {i}) f = refl
r-Id (SET {i}) f = refl
ass (SET {i}) f g h = refl


J-lemma1 : ∀ {i j} (X X' : Type i) (Q : Type i → Type j)
              (F : (A : Type i) → isProp (Q A))
              → (a : Q X) → (b c : Q X')
              → ((X , a) ≡ (X' , b)) ≃ ((X , a) ≡ (X' , c))
J-lemma1 X X' Q F a b c = ((thm2-7-2 (X , a) (X' , c) ^ᵉ) oₑ equiv-fibres-to-equiv-sigma
         (λ { p → transport (λ q → (transport Q p a ≡ q) ≃ (transport Q p a ≡ c)) (F X' c b) erefl})) oₑ
         thm2-7-2 (X , a) (X' , b)

{- Very important, don't delete -}
J-lemma2 : ∀ {i j} (X X' : Type i) (Q : Type i → Type j)
              (F : (A : Type i) → isProp (Q A))
              → (a : Q X) → (b : Q X')
              → (X ≡ X') ≃ ((X , a) ≡ (X' , b))
J-lemma2 X X' Q F a b = (thm2-7-2 (X , a) (X' , b) ^ᵉ) oₑ
         equiv-adjointify ((λ { refl → refl , (F X a b)}) ,
         (λ { (p , u) → p}) ,
         (λ { (refl , refl) → path-equiv-sigma _ _ (refl , (props-are-sets (F X) _ _ _ _))}) ,
         λ { refl → refl})

-- X Q F a b c = ((thm2-7-2 (X , a) (X , c) ^ᵉ) oₑ equiv-fibres-to-equiv-sigma
--             λ { p → transport (λ q → (transport Q p a ≡ q) ≃ (transport Q p a ≡ c)) (F X c b) erefl}) oₑ
--             thm2-7-2 (X , a) (X , b)

-- J-lemma : ∀ {i j} (Q : Type i → Type j)
--               (F : (A : Type i) → isProp (Q A))
--               (w₁ w₂ w₃ : Σ[ A ∈ (Type i) ] Q A)
--               → (pr₁ w₁ ≡ pr₁ w₂) → (pr₁ w₁ ≡ pr₁ w₃)
--               → (w₁ ≡ w₂) ≃ (w₁ ≡ w₃)
-- J-lemma Q F (X , a) (.(pr₁ (X , a)) , b) (.(pr₁ (X , a)) , c) refl refl =  ((thm2-7-2 (X , a) (X , c) ^ᵉ) oₑ equiv-fibres-to-equiv-sigma
--             λ { p → transport (λ q → (transport Q p a ≡ q) ≃ (transport Q p a ≡ c)) (F X c b) erefl}) oₑ
--             thm2-7-2 (X , a) (X , b)
 


-- UA-for-contr : ∀ {i} (X X' : Type i) (pX : isContr X) (pX' : isContr X')
--                → (X ≡ X') ≃ ((X , pX) ≡ (X' , pX'))
-- UA-for-contr X X' pX pX' = J-lemma1 X X' isContr (λ A → isContr-is-prop {_} {A}) pX pX' pX' oₑ {!!}
-- lemma = ∀ {i j} (X : Type i) (P : Type i → Type j) (F :(A : Type i) → isProp (P A))
-- lemma = {!!}


private
  path-equiv-sigma-to-id : {i j : Level} {A : Type i} {P : A → Type j}
                           {w w' : Σ[ x ∈ A ] (P x)}
                           → (w ≡ w') ≡ (Σ[ p ∈ (pr₁ w ≡ pr₁ w') ] (transport P p (pr₂ w) ≡ (pr₂ w')))
  path-equiv-sigma-to-id  = ua (thm2-7-2 _ _)
-- weq1 : ∀ {i} (X X' : Type i) (pX : isProp X) (pX' : isProp X')
--        → ((X , pX) ≡ (X' , pX')) ≃ (Σ[ w ∈ (X ≡ X') ] transport isProp w pX ≡ pX')
-- weq1 = ?

-- Prop-is-set : ∀ {i} → isSet (Prop_ i)
-- Prop-is-set (A , pA) (B , PB) = transport (λ  Z → (p q : Z) → p ≡ q) (path-equiv-sigma-to-id ^)
--             λ { (p , b) (q , c) → path-equiv-sigma _ _ ({!!} , props-are-sets (isProp-is-prop B) _ _ _ _ )}


UA-for-predicates : ∀ {i} (X X' : Type i) (pX : isProp X) (pX' : isProp X')
                    → (X ≃ X') ≃ ((X , pX) ≡ (X' , pX')) 
UA-for-predicates X X' pX pX' = J-lemma2 X X' isProp (λ A → isProp-is-prop A) pX pX' oₑ (univalence ^ᵉ)



univalenceweq : ∀{i} (X X' : Type i)
                → (X ≡ X') ≃ (X ≃ X')
univalenceweq X X' = univalence


-- lemma-1 : ∀ {i j} (UU : Type i) (P : UU → Type j) 
--           → ((A : UU) → isProp (P A)) → (X Y : Σ[ A ∈ UU ] P A)
--           → (X ≡ Y) ≃ (pr₁ X ≡ pr₁ Y)
-- lemma-1 UU P F (A , H1) (B , H2) = {!!} ^ᵉ
--(λ H → ((λ { refl → refl }) o (λ { refl → path-equiv-sigma (A , H1) (A , H) (refl , F A H1 H)})) refl ≡ id refl)
UA-for-sets : ∀ {i} (X X' : Set_ i) 
              → (X ≡ X') ≃ (pr₁ X ≃ pr₁ X')
UA-for-sets {i} (X₁ , a) (X₂ , b) = (J-lemma2 X₁ X₂ isSet (λ A → isSet-is-prop A) a b oₑ (univalence ^ᵉ)) ^ᵉ
set-equiv-iso-qinv : ∀ {i} (A B : ob (SET {i})) → (qequiv (pr₁ A) (pr₁ B)) ≃ (iso {_} {_} {SET {i}} A B)
set-equiv-iso-qinv {i} (X , a) (X' , b) = equiv-adjointify ((λ { (f , g , α , β) → f , (g , ((funext α) , (funext β)))}) ,
                   ((λ { (f , g , α , β) → f , (g , ((happly α) , (happly β)))}) ,
                   ((λ { (f , g , α , β) → path-equiv-sigma _ _ (refl ,
                     transport (λ F → (g , funext (happly α) , F) ≡ (g , α , β)) (pr₁ ( (pr₂ happly-isEquiv)) β ^) (transport (λ F → (g , F , id β) ≡ (g , α , β)) (pr₁ (pr₂ happly-isEquiv) α ^) refl))}) ,
                   λ { (f , g , α , β) → path-equiv-sigma _ _ (refl , (transport (λ F → (g , happly (funext α) , F)  ≡ (g , α , β)) (pr₁ (pr₂ (pr₂ happly-isEquiv)) β ^) (transport (λ F → (g , F , id β) ≡ (g , α , β)) (pr₁ (pr₂ (pr₂ happly-isEquiv)) α ^) refl)))})))


qinv-of-sets-is-prop : ∀ {i} {A B : Set_ i} (f : pr₁ A → pr₁ B)
                       → isProp (qinv f)
qinv-of-sets-is-prop {i} {X , a} {Y , b} f (g , α , β) (g' , α' , β') = path-equiv-sigma _ _ ((funext (λ y → β' (g y) ^ ∘ ap g' (α y))) , path-equiv-sigma _ _ ((funextD (λ y → b _ _ _ _)) , funextD λ x → a _ _ _ _))


set-id-equiv-iso : ∀ {i} (A B : ob (SET {i})) → (A ≡ B) ≃ (iso {_} {_} {SET {i}} A B)
set-id-equiv-iso {i} (X , a) (X' , b) = (set-equiv-iso-qinv (X , a) (X' , b) oₑ
                 equiv-fibres-to-equiv-sigma λ f → props-equiv (isEquiv-is-prop f) (qinv-of-sets-is-prop {i} {X , a} {X' , b} f) isEquiv-to-qinv qinv-to-ishae) oₑ
                 UA-for-sets (X , a) (X' , b)

J-lemma3 : ∀ {i} (A B : ob (SET {i}))
           → pr₁ (set-id-equiv-iso A B) ≡ id-to-iso (SET {i}) {A} {B}
J-lemma3 {i} (X , a) (X' , b) = funext λ { refl → path-equiv-sigma _ _ ((funext (λ x → refl)) , iso-of-f-is-prop {_} {_} {SET {i}} {(X , a)} {(X' , b)} _ _ _)}


SET-is-category : ∀ {i} → isCat (SET {i})
univ (SET-is-category {i}) A B = transport (λ f → isEquiv f) (J-lemma3 A B) (pr₂ (set-id-equiv-iso A B))
