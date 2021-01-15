{-# OPTIONS --without-K  #-}
module UniAgda.categories.categories.initial where

open import UniAgda.categories.category public

𝟘 : Precategory {lzero} {lzero}
𝟘 =
  Empty ,
  (λ a b → Empty) ,
  (λ { () b x y p q}) ,
  ((λ { {()}})) ,
  (λ { () x₁}) ,
  (λ { ()}) ,
  (λ { ()}) ,
  λ { () g h}
-- ob 𝟘 = Empty
-- hom 𝟘 a b = Empty
-- hom-set 𝟘 a b = empty-is-set
-- Id 𝟘 {()}
-- comp 𝟘 () g
-- l-Id 𝟘 ()
-- r-Id 𝟘 ()
-- ass 𝟘 () g h

-- 𝟘-is-category : isCategory 𝟘
-- univ 𝟘-is-category () b
