{-# OPTIONS --without-K #-}
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
    iii : {x : X.ob} (α : P x) → H α α X.Id
    iv : {x y z : X.ob} (α : P x) (β : P y) (γ : P z) (f : X.hom x y) (g : X.hom y z)
         → H α β f → H β γ g → H α γ (g X.<o> f)
