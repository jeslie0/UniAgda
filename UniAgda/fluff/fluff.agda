{-# OPTIONS --without-K #-}
module UniAgda.fluff.fluff where

open import UniAgda.everything public



J-lemma1 : ∀ {i j} (X X' : Type i) (Q : Type i → Type j)
              (F : (A : Type i) → isProp (Q A))
              → (a : Q X) → (b c : Q X')
              → ((X , a) ≡ (X' , b)) ≃ ((X , a) ≡ (X' , c))
J-lemma1 X X' Q F a b c = ((thm2-7-2 (X , a) (X' , c) ^ᵉ) oₑ equiv-fibres-to-equiv-sigma
         (λ { p → transport (λ q → (transport Q p a ≡ q) ≃ (transport Q p a ≡ c)) (F X' c b) erefl})) oₑ
         thm2-7-2 (X , a) (X' , b)

UA-for-predicates : ∀ {i} (X X' : Type i) (pX : isProp X) (pX' : isProp X')
                    → (X ≃ X') ≃ ((X , pX) ≡ (X' , pX')) 
UA-for-predicates X X' pX pX' = id-equiv-to-prop-on-type X X' isProp (λ A → isProp-is-prop A) pX pX' oₑ (univalence ^ᵉ)



univalenceweq : ∀{i} (X X' : Type i)
                → (X ≡ X') ≃ (X ≃ X')
univalenceweq X X' = univalence


