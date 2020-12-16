{-# OPTIONS --without-K --type-in-type #-}
module UniAgda.experimental.exp where

open import UniAgda.core.CORE public

record precat {i j} : Type (lsuc (i ⊔ j)) where
  no-eta-equality
  field
    ob : Type i
    hom : (a b : ob) → Type j
    hom-set : (a b : ob) → isSet (hom a b)
    Id : {a : ob} → (hom a a)
    comp : {a b c : ob} → (hom b c) → hom a b → hom a c
    l-Id : {a b : ob} (f : hom a b) → comp f Id ≡ f
    r-Id : {a b : ob} (f : hom a b) → comp Id f ≡ f
    ass : {a b c d : ob} (f : hom a b) (g : hom b c) (h : hom c d) → comp h (comp g f) ≡ comp (comp h g) f

-- iso : ∀ {i j} {∁ : precat {i} {j}} {a b : precat.ob ∁}
--       (f : precat.hom ∁ a b)
--       → Type j
-- iso {_} {_} {∁} {a} {b} f = Σ[ g ∈ (precat.hom ∁ b a) ] ((precat._$o_ ∁ f g ≡ precat.Id ∁) × (precat._$o_ ∁ g f ≡ precat.Id ∁))

open precat public


is-iso : ∀ {i j} {∁ : precat {i} {j}} {a b : ob ∁}
      (f : hom ∁ a b)
      → Type j
is-iso {i} {j} {∁} {a} {b} f = Σ[ g ∈ (hom ∁ b a) ] ((comp ∁ f g ≡ precat.Id ∁) × (comp ∁ g f ≡ precat.Id ∁))


iso : ∀ {i j} {∁ : precat {i} {j}}
      (a b : ob ∁)
      → Type j
iso {i} {j} {∁} a b = Σ[ f ∈ (hom ∁ a b) ] (is-iso {i} {j} {∁} {a} {b} f)


{- iso is equivalence relation -}

iso-refl : ∀ {i j} {∁ : precat {i} {j}}
           (a : ob ∁)
           -> iso {_} {_} {∁} a a
iso-refl {i} {j} {∁} a = (Id ∁) , ((Id ∁) , ((l-Id ∁ (Id ∁)) , (r-Id ∁ (Id ∁))))

iso-sym : ∀ {i j} {∁ : precat {i} {j}}
          {a b : ob ∁}
          -> (iso {_} {_} {∁} a b) -> (iso {_} {_} {∁} b a)
iso-sym {i} {j} {∁} {a} {b} (f , g , x , y) = g , (f , (y , x))

iso-trans : ∀ {i j} {∁ : precat {i} {j}}
            {a b c : ob ∁}
            -> (iso {_} {_} {∁} a b) -> (iso {_} {_} {∁} b c) -> (iso {_} {_} {∁} a c) 
iso-trans {i} {j} {∁} {a} {b} {c} (f , g , x , y) (f' , g' , x' , y') = (comp ∁ f' f) ,
                                                                        ((comp ∁ g g') ,
                                                                        (((ass ∁ g' g _) ∘ transport (λ Z → comp ∁ Z g' ≡ Id ∁) (ass ∁ _ _ _) (transport (λ Z → comp ∁ (comp ∁ f' Z ) g' ≡ Id ∁) (x ^) (transport (λ Z → comp ∁ Z g' ≡ Id ∁) (l-Id ∁ f' ^) x')) ) ,
                                                                        ((ass ∁ _ g' g) ^ ∘ transport (λ Z → comp ∁ g Z ≡ Id ∁) (ass ∁ _ _ _ ^) (transport (λ Z → comp ∁ g (comp ∁ Z f) ≡ Id ∁) (y' ^) (transport (λ Z → comp ∁ g Z ≡ Id ∁) (r-Id ∁ f ^) y)) )))


iso-of-f-is-prop : ∀ {i j} {∁ : precat {i} {j}} {a b : ob ∁} (f : hom ∁ a b)
             → isProp (is-iso {i} {j} {∁} {a} {b} f)
iso-of-f-is-prop {i} {j} {∁} {a} {b} f (g , η , ε) (g' , η' , ε') =  path-equiv-sigma _ _
           (r-Id ∁ g ^ ∘ transport (λ X → comp ∁ X g ≡ g') (ε') ((ass ∁ _ _ _) ^ ∘ transport (λ X → comp ∁ g' X ≡ g') (η ^) (l-Id ∁ g') ) , path-equiv-prod ((hom-set ∁ _ _ _ _ _ η') , hom-set ∁ _ _ _ _ _ ε')) 

iso-is-set : ∀ {i j} {∁ : precat {i} {j}}
             (a b : ob ∁)
             → isSet (iso {_} {_} {∁} a b)
iso-is-set {_} {_} {∁} a b = prop-fibres-totalspace-set (hom-set ∁ a b) λ x → iso-of-f-is-prop {_} {_} {∁} x


id-to-iso : ∀ {i j} (∁ : precat {i} {j}) {a b : ob ∁}
            → (a ≡ b) → (iso {i} {j} {∁} a b)
id-to-iso {i} {j} ∁ refl = (Id ∁) , ((Id ∁) , (l-Id ∁ (Id ∁) , r-Id ∁ (Id ∁)))

record isCat {i j} (∁ : precat {i} {j}) : Type (lsuc (i ⊔ j)) where
  field
    univ : (a b : ob ∁) → isequiv (id-to-iso {i} {j} ∁ {a} {b})

open isCat public

lemma : ∀ {i j} {∁ : precat {i} {j}} {H : isCat ∁}
        → (a b : ob ∁) → iso {_} {_} {∁} a b → a ≡ b
lemma {i} {j} {∁} {H} a b x = pr₁ (univ H a b) x

cat-ob-is1type : ∀ {i j} {∁ : precat {i} {j}} {H : isCat ∁} → is1type (ob ∁)
cat-ob-is1type {i} {j} {∁} {H} a b = transport (λ Z → isSet Z) (ua (id-to-iso ∁ , (univ H a b)) ^) (iso-is-set {_} {_} {∁} a b)



record functor {i j k l} (A : precat {i} {j}) (B : precat {k} {l}) : Type (i ⊔ j ⊔ k ⊔ l) where
  no-eta-equality
  field
    F-ob : ob A → ob B
    F-hom : {a b : ob A} → hom A a b → hom B (F-ob a) (F-ob b)
    F-id : {a : ob A} → F-hom (Id A {a}) ≡ (Id B {F-ob a})
    F-nat : {a b c : ob A} (g : hom A b c) (f : hom A a b) → F-hom (comp A g f) ≡ comp B (F-hom g) (F-hom f)

open functor public

record nat-trans {i j k l} {A : precat {i} {j}} {B : precat {j} {k}} (F G : functor A B) : Type (i ⊔ j ⊔ k ⊔ l) where
  no-eta-equality
  field
    α-ob : (x : ob A) → hom B (F-ob F x) (F-ob G x)
    α-hom : {x y : ob A} (f : hom A x y) → comp B (α-ob y) (F-hom F f) ≡ comp B (F-hom G f) (α-ob x)

open nat-trans public



-- functor-precat : ∀ {i j k l} (A : precat {i} {j}) (B : precat {k} {l}) → precat {i ⊔ j ⊔ k ⊔ l} {i ⊔ j ⊔ k ⊔ l}
-- ob (functor-precat {i} {j} {k} {l} A B) = functor A B
-- hom (functor-precat {i} {j} {k} {l} A B) F G = nat-trans F G
-- hom-set (functor-precat {i} {j} {k} {l} A B) a b x y p q = {!!}
-- α-ob (Id (functor-precat {i} {j} {k} {l} A B)) x = Id B
-- α-hom (Id (functor-precat {i} {j} {k} {l} A B)) f = r-Id B _ ∘ l-Id B _ ^
-- α-ob (comp (functor-precat {i} {j} {k} {l} A B) α β) x = comp B (α-ob α x) (α-ob β x)
-- α-hom (comp (functor-precat {i} {j} {k} {l} A B) α β) f = {!!}
-- l-Id (functor-precat {i} {j} {k} {l} A B) f = {!!}
-- r-Id (functor-precat {i} {j} {k} {l} A B) = {!!}
-- ass (functor-precat {i} {j} {k} {l} A B) = {!!}













-- Set-is-1type : ∀ {i} → is1type (Set_ i)
-- Set-is-1type {i} a b = {!!}



{- Set is a cat -}
Set-precat : ∀ {i} → precat
ob (Set-precat {i}) = Set_ i
hom (Set-precat {i}) a b = (pr₁ a) → (pr₁ b)
hom-set (Set-precat {i}) a b = func-of-sets-is-set (pr₂ b)
Id (Set-precat {i}) = id
comp (Set-precat {i}) = _o_
l-Id (Set-precat {i}) f = refl
r-Id (Set-precat {i}) f = refl
ass (Set-precat {i}) f g h = refl

private
 Set-is-cat-hom1 : {i : Level} {a b : ob (Set-precat {i})}
                   -> (iso {_} {_} {Set-precat {i}} a b) -> (a ≡ b)
 Set-is-cat-hom1 {i} {a} {b} (f , g , x , y) = path-equiv-sigma _ _ ((ua (equiv-adjointify (f , (g , ((happly x) , (happly y)))))) , isSet-is-prop _ _ _)

 Set-is-cat-hom2 : {i : Level} {a b : ob (Set-precat {i})}
                   -> (a == b) -> (iso {_} {_} {Set-precat {i}} a b)
 Set-is-cat-hom2 {i} {a} {.a} refl = iso-refl {_} {_} {Set-precat {i}} a

 -- Set-is-cat-η : ∀ {i} {a b : ob (Set-precat {i})}
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


Set-is-cat : ∀ {i} → isCat (Set-precat {i})
univ (Set-is-cat {i}) (a , H₁) (b , H₂) = isequiv-adjointify ((λ {(f , g , h1 , h2) → lemma3-5-1 isSet-is-prop _ _ (ua (equiv-adjointify (f , (g , ((happly h1) , (happly h2))))))}) ,
                 (λ { (f , g , h₁ , h₂) → path-equiv-sigma _ _ ((funext (λ x → {!!})) , iso-of-f-is-prop {_} {_} {Set-precat {i}} {(a , H₁)} {(b , H₂)} f _ _)}),
     λ { refl → transport (λ Z → lemma3-5-1 isSet-is-prop (a , H₁) (a , H₂) Z ≡ refl) (ua-id) (lemma2 isSet-is-prop (a , H₁)) })





foo1 : (X Y : Set_ lzero) (f : pr₁ X → pr₁ Y) → qinv f → iso {_} {_} {Set-precat {lzero}} X Y
foo1 (A , H₁) (B , H₂) f (g , α , β) = f , (g , ((funext α) , (funext β)))

foo2 : (X Y : Set_ lzero) → pr₁ X ≃ pr₁ Y → iso {_} {_} {Set-precat {lzero}} X Y
foo2 (A , H₁) (B , H₂) (f , g , α , β , γ) = f , (g , ((funext β) , (funext α)))


foo3 : (X Y : Set_ lzero) → iso {_} {_} {Set-precat {lzero}} X Y → pr₁ X ≃ pr₁ Y 
foo3 (A , H₁) (B , H₂) (f , g , α , β) = equiv-adjointify (f , (g , ((happly α) , (happly β)))) 



-- foo4 : (X Y : Set_ lzero) → (pr₁ X ≃ pr₁ Y) ≃ (iso {_} {_} {Set-precat {lzero}} X Y)
-- foo4 (A , H₁) (B , H₂) = equiv-adjointify ((foo2 (A , H₁) (B , H₂)) , foo3 (A , H₁) (B , H₂) , (λ { (f , g , α , β) → lemma3-5-1 (iso-of-f-is-prop {lzero} {lzero} {Set-precat {lzero}} {(A , H₁)} {(B , H₂)}) _ _ refl}) ,
--   λ { (f , g , α , β , γ) → lemma3-5-1 isequiv-is-prop _ _  refl})




ex3-4 : ∀ {i} (A : Type i)
        → isProp A ↔ isContr (A → A)
ex3-4 A = (λ F → id , λ f → funext λ x → F x (f x)) , λ { (f , F) x y → happly (F id) x ^ ∘ happly (F (λ _ → y)) x}

ex3-5-i : ∀ {i} (A : Type i)
        → isProp A → (A → isContr A)
ex3-5-i A F x = x , (λ y → F x y)

ex3-5-ii : ∀ {i} (A : Type i)
           → (A → isContr A) → isProp A
ex3-5-ii A F x y = (pr₂ (F x) x ^) ∘ pr₂ (F x) y

ex3-5-iii : ∀ {i} (A : Type i)
            → ex3-5-i A o ex3-5-ii A ~ id
ex3-5-iii A F = funextD λ x → isContr-is-prop _ _

ex3-5-iv : ∀ {i} (A : Type i)
           → ex3-5-ii A o ex3-5-i A ~ id
ex3-5-iv A F = funextD λ x → funextD λ y → props-are-sets F _ _ _ _ 


ex3-5 : ∀ {i} (A : Type i)
        → isProp A ≃ (A → isContr A)
ex3-5 A = equiv-adjointify (ex3-5-i A , (ex3-5-ii A) , ((ex3-5-iii A) , (ex3-5-iv A)))


isequiv-is-prop : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
                  → isProp (isequiv f)
isequiv-is-prop {i} {j} {A} {B} f = pr₁ (pr₂ (ex3-5 (isequiv f))) λ x → {!!}
