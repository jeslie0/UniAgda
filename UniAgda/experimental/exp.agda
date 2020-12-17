{-# OPTIONS --without-K --type-in-type #-}
module UniAgda.experimental.exp where

open import UniAgda.everything public




-- Set-is-1type : ∀ {i} → is1type (Set_ i)
-- Set-is-1type {i} a b = {!!}



{- Set is a cat -}
Set-Precategory : ∀ {i} → Precategory
ob (Set-Precategory {i}) = Set_ i
hom (Set-Precategory {i}) a b = (pr₁ a) → (pr₁ b)
hom-set (Set-Precategory {i}) a b = func-of-sets-is-set (pr₂ b)
Id (Set-Precategory {i}) = id
comp (Set-Precategory {i}) = _o_
l-Id (Set-Precategory {i}) f = refl
r-Id (Set-Precategory {i}) f = refl
ass (Set-Precategory {i}) f g h = refl

private
 Set-is-cat-hom1 : {i : Level} {a b : ob (Set-Precategory {i})}
                   -> (iso {_} {_} {Set-Precategory {i}} a b) -> (a ≡ b)
 Set-is-cat-hom1 {i} {a} {b} (f , g , x , y) = path-equiv-sigma _ _ ((ua (equiv-adjointify (f , (g , ((happly x) , (happly y)))))) , isSet-is-prop _ _ _)

 Set-is-cat-hom2 : {i : Level} {a b : ob (Set-Precategory {i})}
                   -> (a == b) -> (iso {_} {_} {Set-Precategory {i}} a b)
 Set-is-cat-hom2 {i} {a} {.a} refl = iso-refl {_} {_} {Set-Precategory {i}} a

 -- Set-is-cat-η : ∀ {i} {a b : ob (Set-Precategory {i})}
 --                → homotopy (Set-is-cat-hom1 {i} {a} {b} o Set-is-cat-hom2 {i} {a} {b}) id
 -- Set-is-cat-η {i} {a} {b} = {!transport (λ Z → (p : Z) → (Set-is-cat-hom1 o Set-is-cat-hom2) p ≡ id p)!}



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


Set-is-cat : ∀ {i} → isCat (Set-Precategory {i})
univ (Set-is-cat {i}) (a , H₁) (b , H₂) = isEquiv-adjointify ((λ {(f , g , h1 , h2) → lemma3-5-1 isSet-is-prop _ _ (ua (equiv-adjointify (f , (g , ((happly h1) , (happly h2))))))}) ,
                 (λ { (f , g , h₁ , h₂) → path-equiv-sigma _ _ ((funext (λ x → {!!})) , iso-of-f-is-prop {_} {_} {Set-Precategory {i}} {(a , H₁)} {(b , H₂)} f _ _)}),
     λ { refl → transport (λ Z → lemma3-5-1 isSet-is-prop (a , H₁) (a , H₂) Z ≡ refl) (ua-id) (lemma2 isSet-is-prop (a , H₁)) })





foo1 : (X Y : Set_ lzero) (f : pr₁ X → pr₁ Y) → qinv f → iso {_} {_} {Set-Precategory {lzero}} X Y
foo1 (A , H₁) (B , H₂) f (g , α , β) = f , (g , ((funext α) , (funext β)))

foo2 : (X Y : Set_ lzero) → pr₁ X ≃ pr₁ Y → iso {_} {_} {Set-Precategory {lzero}} X Y
foo2 (A , H₁) (B , H₂) (f , g , α , β , γ) = f , (g , ((funext β) , (funext α)))


foo3 : (X Y : Set_ lzero) → iso {_} {_} {Set-Precategory {lzero}} X Y → pr₁ X ≃ pr₁ Y 
foo3 (A , H₁) (B , H₂) (f , g , α , β) = equiv-adjointify (f , (g , ((happly α) , (happly β)))) 



-- foo4 : (X Y : Set_ lzero) → (pr₁ X ≃ pr₁ Y) ≃ (iso {_} {_} {Set-Precategory {lzero}} X Y)
-- foo4 (A , H₁) (B , H₂) = equiv-adjointify ((foo2 (A , H₁) (B , H₂)) , foo3 (A , H₁) (B , H₂) , (λ { (f , g , α , β) → lemma3-5-1 (iso-of-f-is-prop {lzero} {lzero} {Set-Precategory {lzero}} {(A , H₁)} {(B , H₂)}) _ _ refl}) ,
--   λ { (f , g , α , β , γ) → lemma3-5-1 isEquiv-is-prop _ _  refl})





