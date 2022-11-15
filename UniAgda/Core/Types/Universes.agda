{-# OPTIONS --without-K --no-import-sorts --safe --no-import-sorts #-}
module UniAgda.Core.Types.Universes where

-- This is mostly taken from the Cubical library and Egbert Rijke's HoTT library.

open import Agda.Primitive public
  using    ( Level ; lzero ; lsuc ; _⊔_)
  renaming ( Set  to Type
           ; Setω to Typeω )

data raise (l : Level) {l1 : Level} (A : Type l1) : Type (l1 ⊔ l) where
  map-raise : A → raise l A

map-inv-raise :
  {l l1 : Level} {A : Type l1} → raise l A → A
map-inv-raise (map-raise x) = x

typeOf : ∀ {i} {A : Type i}
              (a : A)
              → Type i
typeOf {A = A} a = A
