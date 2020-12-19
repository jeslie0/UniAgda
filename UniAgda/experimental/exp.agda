{-# OPTIONS --without-K --type-in-type #-}
module UniAgda.experimental.exp where

open import UniAgda.everything public




-- Set-is-1type : ∀ {i} → is1type (Set_ i)
-- Set-is-1type {i} a b = {!!}



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

private
 Set-is-cat-hom1 : {i : Level} {a b : ob (SET {i})}
                   -> (iso {_} {_} {SET {i}} a b) -> (a ≡ b)
 Set-is-cat-hom1 {i} {a} {b} (f , g , x , y) = path-equiv-sigma _ _ ((ua (equiv-adjointify (f , (g , ((happly x) , (happly y)))))) , (isSet-is-prop _ _ _))


 Set-is-cat-hom2 : {i : Level} {a b : ob (SET {i})}
                   -> (a ≡ b) -> (iso {_} {_} {SET {i}} a b)
 Set-is-cat-hom2 {i} {a} {.a} refl = iso-refl {_} {_} {SET {i}} a

 Set-is-1type : ∀ {i} → is1type (Set_ i)
 Set-is-1type = {!!}


 Set-is-cat-η : ∀ {i} {a b : ob (SET {i})}
                → (Set-is-cat-hom1 {i} {a} {b} o Set-is-cat-hom2 {i} {a} {b}) ~ id
 Set-is-cat-η {i} {a , H1} {.a , .H1} refl = {!!}



private
  path-equiv-sigma-to-id : {i j : Level} {A : Type i} {P : A → Type j}
                           {w w' : Σ[ x ∈ A ] (P x)}
                           → (w ≡ w') ≡ (Σ[ p ∈ (pr₁ w ≡ pr₁ w') ] (transport P p (pr₂ w) ≡ (pr₂ w')))
  path-equiv-sigma-to-id  = ua (thm2-7-2 _ _)


lemma3 : {i j : Level} {A : Type i} {P : A → Type j}
                   → (f : (x : A) → isProp (P x))
                   → (x : A) (u : P x)
                   → f x u u ≡ refl
lemma3 {i} {j} {A} {P} f x u = props-are-sets (f x) u u (f x u u) refl



lemma2 : {i j : Level} {A : Type i} {P : A → Type j}
                   → (f : (x : A) → isProp (P x)) → (u : Σ[ x ∈ A ] (P x))
                   → lemma3-5-1 f u u refl ≡ refl
lemma2 f (a , b) = transport (λ Z → path-equiv-sigma _ _ (refl , Z) ≡ refl) (lemma3 f (a) (b) ^) refl


Set-is-cat : ∀ {i} → isCat (SET {i})
univ (Set-is-cat {i}) (a , H₁) (b , H₂) = isequiv-adjointify ((λ {(f , g , h1 , h2) → lemma3-5-1 isSet-is-prop _ _ (ua (equiv-adjointify (f , (g , ((happly h1) , (happly h2))))))}) ,
                 (λ { (f , g , h₁ , h₂) → path-equiv-sigma _ _ (funext (λ y → {!!}) , iso-of-f-is-prop {_} {_} {SET {i}} {(a , H₁)} {(b , H₂)} f _ _)}),
     λ { refl → transport (λ Z → lemma3-5-1 isSet-is-prop (a , H₁) (a , H₂) Z ≡ refl) (ua-id) (lemma2 isSet-is-prop (a , H₁)) })





foo1 : (X Y : Set_ lzero) (f : pr₁ X → pr₁ Y) → qinv f → iso {_} {_} {SET {lzero}} X Y
foo1 (A , H₁) (B , H₂) f (g , α , β) = f , (g , ((funext α) , (funext β)))

foo2 : (X Y : Set_ lzero) → pr₁ X ≃ pr₁ Y → iso {_} {_} {SET {lzero}} X Y
foo2 (A , H₁) (B , H₂) (f , g , α , β , γ) = f , (g , ((funext β) , (funext α)))


foo3 : (X Y : Set_ lzero) → iso {_} {_} {SET {lzero}} X Y → pr₁ X ≃ pr₁ Y 
foo3 (A , H₁) (B , H₂) (f , g , α , β) = equiv-adjointify (f , (g , ((happly α) , (happly β)))) 



foo4 : (X Y : Set_ lzero) → (pr₁ X ≃ pr₁ Y) ≃ (iso {_} {_} {SET {lzero}} X Y)
foo4 (A , H₁) (B , H₂) = equiv-adjointify ((foo2 (A , H₁) (B , H₂)) , foo3 (A , H₁) (B , H₂) , (λ { (f , g , α , β) → lemma3-5-1 (iso-of-f-is-prop {lzero} {lzero} {SET {lzero}} {(A , H₁)} {(B , H₂)}) _ _ refl}) ,
  λ { (f , g , α , β , γ) → lemma3-5-1 isEquiv-is-prop _ _  refl})

foo5 : (X Y : Set_ lzero) → (pr₁ X ≃ pr₁ Y) ≡ (iso {_} {_} {SET {lzero}} X Y)
foo5 X Y = ua (foo4 X Y)

foo6 : (X Y : Set_ lzero) → (pr₁ X ≡ pr₁ Y) ≡ (iso {_} {_} {SET {lzero}} X Y)
foo6 X Y = ua univalence ∘ foo5 X Y


-- Set-is-cat : ∀ {i} → isCat (SET {i})
-- univ (Set-is-cat {i}) (A , H₁) (B , H₂) = isequiv-adjointify ((λ { x → path-equiv-sigma _ _ ((ua (pr₁ (foo4 (A , H₁) (B , H₂) ^ᵉ) x)) , isSet-is-prop _ _ _)}) ,
--      ((λ { (f , g , α , β) → path-equiv-sigma _ _ (funext (λ x → {!!}) , iso-of-f-is-prop {_} {_} {SET {i}} f _ _)}) ,
--      λ x → {!!}))

-- iso-to-id-SET : ∀ {i} {A B : ob (SET {i})}
--                 iso A B → A ≡ B
-- iso-to-id-SET = {!!}

-- univalenceweq : ∀ {i j} (X : Type i) (X' : Type j)
--                 → (X ≃ X') ≃ (X ≃ X')
-- univalenceweq X X' = {!!}


