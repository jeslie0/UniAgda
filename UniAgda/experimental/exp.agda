{-# OPTIONS --without-K --no-import-sorts #-}
module UniAgda.experimental.exp where
open import UniAgda.Core.Everything
open import UniAgda.Categories.Category
--SIP



record Notion-of-Structure {i j k l : Level} (X : Precategory i j) : Type (lsuc (i ⊔ j ⊔ k ⊔ l)) where
  eta-equality
  module X = Precategory X
  field
    P : X.ob → Type k
    H : {x y : X.ob} (α : P x) (β : P y) (f : X.hom x y) → Type l
    H-is-prop : {x y : X.ob} (α : P x) (β : P y) (f : X.hom x y) → isProp (H α β f)
    H-id : {x : X.ob} (α : P x) → H α α X.Id
    H-comp : {x y z : X.ob} (α : P x) (β : P y) (γ : P z) (f : X.hom x y) (g : X.hom y z)
         → H α β f → H β γ g → H α γ (g X.<o> f)

  _≤_ : {x : X.ob} (α β : P x) → Type l
  α ≤ β = H α β X.Id

  isStandard : Type (i ⊔ k ⊔ l)
  isStandard = (x : X.ob) (α β : P x) → (α ≤ β) → (β ≤ α) → (α ≡ β)


Str : ∀ {i j k l} {X : Precategory i j} (PH : Notion-of-Structure {i} {j} {k} {l} X) → Precategory (i ⊔ k) (j ⊔ l)
Str {X = X} PH =
  let module X = Precategory X
      module PH = Notion-of-Structure PH
  in record
       { ob = Σ[ x ∈ X.ob ] (PH.P x)
       ; hom = λ { (x , α) (y , β) → Σ[ f ∈ (X.hom x y) ] PH.H α β f}
       ; hom-set = λ { (x , α) (y , β) →
                     prop-fibres-totalspace-set (X.hom-set x y) (PH.H-is-prop α β )}
       ; Id = λ { {x , α} → X.Id , PH.H-id α}
       ; comp = λ { {x , α} {y , β} {z , γ} (g , G) (f , F) → (g X.<o> f) , PH.H-comp α β γ f g F G}
       ; IdL = λ { {x , α} {y , β} (f , F) → path-equiv-sigma ((X.IdL f) , (PH.H-is-prop α β f _ F))}
       ; IdR =  λ { {x , α} {y , β} (f , F) → path-equiv-sigma ((X.IdR f) , (PH.H-is-prop α β f _ F))}
       ; Assoc = λ { {x , α} {y , β} {z , γ} {w , δ} (f , F) (g , G) (h , H') →
                     path-equiv-sigma ((X.Assoc f g h) , (PH.H-is-prop α δ _ _ _))}
       }


private
  helper1 : ∀ {i j k l}
            (X : Precategory i j)
            (PH : Notion-of-Structure {i} {j} {k} {l} X) (Stdn : Notion-of-Structure.isStandard PH)
            (x y : Precategory.ob (Str PH) ) (p : pr₁ x ≡ pr₁ y) →
            Notion-of-Structure.H PH (pr₂ x) (pr₂ y) (pr₁ (Precategory.id-to-iso X p)) →
            Notion-of-Structure.H PH (pr₂ y) (pr₂ x) (pr₁ (Precategory.id-to-iso X (p ^)))
            → x ≡ y
  helper1 X PH Stdn (x , α) (x , β) refl A B =
    path-equiv-sigma (refl , (Stdn x α β A B))


Typeof : ∀ {i} {A : Type i}
         (a : A)
         → Type i
Typeof {A = A} a = A

open Precategory
open Notion-of-Structure

sip-map1 : ∀ {i j k l}
           (X : Precategory i j) (univ : isCategory X)
           (PH : Notion-of-Structure {i} {j} {k} {l} X) (Stdn : Notion-of-Structure.isStandard PH)
           (x y : Precategory.ob (Str PH)) → Precategory.iso (Str PH) x y → x ≡ y
sip-map1 X univ PH Stdn (x , α) (y , β) ((f , F) , (g , G) , η , ϵ) =
  let p = pr₁ (univ x y) (f , g , ap pr₁ η , ap pr₁ ϵ)
  in
    path-equiv-sigma (p ,
      {!Stdn!})




-- SIP : ∀ {i j k l}
--       (X : Precategory i j) (univ : isCategory X)
--       (PH : Notion-of-Structure {i} {j} {k} {l} X) → (Stdn : Notion-of-Structure.isStandard PH)
--       → isCategory (Notion-of-Structure.Precategory-of-Structures PH)
-- SIP X univ PH Stdn (x , α) (y , β) =
--   let module X = Precategory X
--       module PH = Notion-of-Structure PH
--   in isequiv-adjointify ({!!} , {!!})
    
--   --   path-equiv-sigma (pr₁ (univ x y) (f , g , (ap pr₁ η) , (ap pr₁ ϵ)) ,
--   --     {!!})}) ,
--   --   (λ x₁ → {!!}) ,
--   --   (λ x₁ → {!!})) 
