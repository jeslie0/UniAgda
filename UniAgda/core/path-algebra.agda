{-

This file contains lots of tools for manipulating identities with paths.

-}

{-# OPTIONS --without-K #-}
module UniAgda.core.path-algebra where
open import UniAgda.core.primitives public

-- Groupoid properties

ass-l : ∀ {i} {A : Type i} {a b c d : A}
        (p : a ≡ b) (q : b ≡ c) (r : c ≡ d)
        → (p ∘ q) ∘ r ≡ p ∘ (q ∘ r)
ass-l refl q r = refl


ass-r : ∀ {i} {A : Type i} {a b c d : A}
        (p : a ≡ b) (q : b ≡ c) (r : c ≡ d)
        → p ∘ (q ∘ r) ≡ (p ∘ q) ∘ r
ass-r refl q r = refl

pp^ : ∀ {i} {A : Type i} {a b : A}
      (p : a ≡ b)
      → p ∘ p ^ ≡ refl
pp^ refl = refl

p^p : ∀ {i} {A : Type i} {a b : A}
      (p : a ≡ b)
      → p ^ ∘ p ≡ refl
p^p refl = refl

p-refl : ∀ {i} {A : Type i} {a b : A}
         (p : a ≡ b)
         → p ∘ refl ≡ p
p-refl refl = refl


refl-p : ∀ {i} {A : Type i} {a b : A}
         (p : a ≡ b)
         → refl ∘ p ≡ p
refl-p refl = refl


-- Cancelling inverses

p^^=p : ∀ {i} {A : Type i} {a b : A}
        (p : a ≡ b)
        → p ^ ^ ≡ p
p^^=p refl = refl

p-p^q=q : ∀ {i} {A : Type i} {a b c : A}
         (p : a ≡ b) (q : a ≡ c)
         → p ∘ p ^ ∘ q ≡ q
p-p^q=q refl q = refl

pp^-q=q : ∀ {i} {A : Type i} {a b c : A}
         (p : a ≡ b) (q : a ≡ c)
         → (p ∘ p ^) ∘ q ≡ q
pp^-q=q refl q = refl

p^-pq=q : ∀ {i} {A : Type i} {a b c : A}
         (p : a ≡ b) (q : b ≡ c)
         → p ^ ∘ p ∘ q ≡ q
p^-pq=q refl q = refl

p^p-q=q : ∀ {i} {A : Type i} {a b c : A}
         (p : a ≡ b) (q : b ≡ c)
         → (p ^ ∘ p) ∘ q ≡ q
p^p-q=q refl q = refl


-- Composites with refl

prefl-q=pq : ∀ {i} {A : Type i} {a b c : A}
             (p : a ≡ b) (q : b ≡ c)
             → (p ∘ refl) ∘ q ≡ p ∘ q
prefl-q=pq refl q = refl


p-reflq=pq : ∀ {i} {A : Type i} {a b c : A}
             (p : a ≡ b) (q : b ≡ c)
             → p ∘ (refl ∘ q) ≡ p ∘ q
p-reflq=pq refl q = refl

-- Moving inverses about

pq=s-to-q=p^s : ∀ {i} {A : Type i} {a b c : A}
                (p : a ≡ b) (q : b ≡ c) (s : a ≡ c)
                → p ∘ q ≡ s → q ≡ p ^ ∘ s
pq=s-to-q=p^s refl q s x = x

pq=s-to-p=sq^ : ∀ {i} {A : Type i} {a b c : A}
                (p : a ≡ b) (q : b ≡ c) (s : a ≡ c)
                → p ∘ q ≡ s → p ≡ s ∘ (q ^)
pq=s-to-p=sq^ refl refl s x = x ∘ p-refl s ^

p=q-to-pr=qr : ∀ {i} {A : Type i} {x y z : A} {p q : x ≡ y}
               (s : p ≡ q) (r : y ≡ z)
               → p ∘ r ≡ q ∘ r
p=q-to-pr=qr refl r = refl

p=rq-to-r^p=q : {i : Level} {A : Type i} {x y z : A} (p : x ≡ y) (q : z ≡ y)
                (r : x ≡ z)
                → (p ≡ r ∘ q) → r ^ ∘ p ≡ q
p=rq-to-r^p=q refl q refl X = X

p^^-to-p : {i : Level} {A : Type i} {x y : A}
           (p : x ≡ y)
           → p ^ ^ ≡ p
p^^-to-p refl = refl

p^^q-to-pq : {i : Level} {A : Type i} {x y z : A}
             (p : x ≡ y) (q : y ≡ z)
             → p ^ ^ ∘ q ≡ p ∘ q
p^^q-to-pq refl refl = refl

p-to-pqq^ : {i : Level} {A : Type i} {x y z : A}
             (p : x ≡ y) (q : y ≡ z)
             → p ≡ p ∘ q ∘ (q ^)
p-to-pqq^ refl refl = refl

p-to-pq^q : {i : Level} {A : Type i} {x y z : A}
             (p : x ≡ y) (q : z ≡ y)
             → p ≡ p ∘ (q ^) ∘ q
p-to-pq^q refl refl = refl

p-to-qq^p : {i : Level} {A : Type i} {x y z : A}
             (p : x ≡ y) (q : x ≡ z)
             → p ≡ q ∘ (q ^) ∘ p
p-to-qq^p refl refl = refl

p-to-q^qp : {i : Level} {A : Type i} {x y z : A}
             (p : x ≡ y) (q : z ≡ x)
             → p ≡ (q ^) ∘ q ∘ p
p-to-q^qp refl refl = refl

p=q-to-rp=rq : {i : Level} {A : Type i} {x y z : A} {p q : x ≡ y}
               (s : p ≡ q) (r : z ≡ x)
               → r ∘ p ≡ r ∘ q
p=q-to-rp=rq refl r = refl

rp=rq-to-p=q : {i : Level} {A : Type i} {x y z : A} (p q : x ≡ y)
               (r : z ≡ x) (s : r ∘ p ≡ r ∘ q)
               → p ≡ q
rp=rq-to-p=q p q refl refl = refl

q^qpr^r-to-p : {i : Level} {A : Type i} {x y z w : A} (p : x ≡ y) (q : w ≡ x ) (r : z ≡ y)
               → (q ^ ∘ q ∘ p ∘ r ^ ∘ r ≡ p)
q^qpr^r-to-p refl refl refl = refl


pr=qr-to-p=q : {i : Level} {A : Type i} {x y z : A} {p q : x ≡ y}
               (r : y ≡ z) (s : p ∘ r ≡ q ∘ r)
               → p ∘ r ≡ q ∘ r
pr=qr-to-p=q refl s = s


prefl-o-prefl^ : {i : Level} {A : Type i} {a : A} {q : a ≡ a}
                     → ((λ { x → p-refl q ∘ x }) o (λ { x → p-refl q ^ ∘ x })) refl ≡ id refl
prefl-o-prefl^ {i} {A} {a} {q} = ass-r (p-refl q) (p-refl q ^) refl ∘ p-refl (p-refl q ∘ p-refl q ^) ∘ pp^ (p-refl q)


prefl^-o-prefl : {i : Level} {A : Type i} {a : A} {q : a ≡ a}
                     → ((λ { x → p-refl q ^ ∘ x }) o (λ { x → p-refl q ∘ x })) refl ≡ id refl
prefl^-o-prefl {i} {A} {a} {q} =  ass-r (p-refl q ^) (p-refl q) refl ∘  p-refl (p-refl q ^ ∘ p-refl q) ∘ p^p (p-refl q)


p^-apIDp-to-refl : {i : Level} {A : Type i} {x y : A}
                   (p : x ≡ y)
                   → p ^ ∘ ap id p ≡ refl
p^-apIDp-to-refl refl = refl


-- Inverses and concatenation

pq-^-to-q^p^ : ∀ {i} {A : Type i} {a b c : A}
               (p : a ≡ b) (q : b ≡ c)
               → (p ∘ q) ^ ≡ q ^ ∘ p ^
pq-^-to-q^p^ refl refl = refl


-- ap properties
apf-pq : ∀ {i j} {A : Type i} {B : Type j} {x y z : A}
         (f : A → B) (p : x ≡ y) (q : y ≡ z)
         → (f [ (p ∘ q) ]) ≡ ((f [ p ]) ∘ (f [ q ]))
apf-pq f refl q = refl

apf-p^ : ∀ {i j} {A : Type i} {B : Type j} {x y : A}
         (f : A → B) (p : x ≡ y)
         → f [ p ^ ] ≡ (f [ p ]) ^
apf-p^ f refl = refl

ap-gf : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} {x y : A}
         (g : B → C) (f : A → B) (p : x ≡ y)
         → (g o f) [ p ] ≡ g [ f [ p ] ] 
ap-gf g f refl = refl

ap-id : ∀ {i} {A : Type i} {x y : A}
        (p : x ≡ y)
        → id [ p ] ≡ p
ap-id refl = refl


ap-idp-p^ : {i : Level} {A : Type i} {x y : A}
            (p : x ≡ y)
            → ((ap id p) ∘ (p ^)) ≡ refl
ap-idp-p^ refl = refl

ap-const : ∀ {i j} {A : Type i} {B : Type j} {x y : A} {p : x ≡ y}
           → (y : B)
           → ap (λ (a : A) → y) p ≡ refl
ap-const {i} {j} {A} {B} {x} {.x} {refl} y₁ = refl

-- Transport properties (2.3)

lift : ∀ {i j} {A : Type i} {P : A → Type j} {x y : A}
       (u : P x) (p : x ≡ y)
       → (x , u) ≡ (y , transport P p u)
lift u refl = refl

lift-comp : ∀ {i j} {A : Type i} {P : A → Type j} {x y : A}
       (u : P x) (p : x ≡ y)
       → pr₁ [ lift {_} {_} {A} {P} u p ] ≡ p
lift-comp u refl = refl

tr-pq : ∀ {i j} {A : Type i} {P : A → Type j} {x y z : A}
        (p : x ≡ y) (q : y ≡ z) (u : P x)
        → transport P (p ∘ q) u ≡ (transport P q (transport P p u))
tr-pq refl q u = refl

tr-Pf : ∀ {i j k} {A : Type i} {B : Type j} {x y : A}
        (P : B → Type k) (f : A → B) (p : x ≡ y) (u : P (f x))
        → transport (P o f) p u ≡ transport P (f [ p ]) u
tr-Pf P f refl u = refl
tr-P-to-Q : ∀ {i j k} {A : Type i} {x y : A} {P : A → Type j} {Q : A → Type k}
            (f : (x : A) → P x → Q x) (p : x ≡ y) (u : P x)
            → transport Q p (f x u) ≡ f y (transport P p u)
tr-P-to-Q f refl u = refl



-- Add in the following and tidy up names
p^q=s-to-q=ps : {i : Level} {A : Type i} {x y z : A} {p : x ≡ y} {q : z ≡ y}
                (r : x ≡ z) (t : r ^ ∘ p ≡ q)
                → p ≡ r ∘ q
p^q=s-to-q=ps refl refl = refl

-- p=rq-to-r^p=q : {i : Level} {A : Type i} {x y z : A} (p : x ≡ y) (q : z ≡ y)
--                 (r : x ≡ z)
--                 → (p ≡ r ∘ q) → r ^ ∘ p ≡ q
-- p=rq-to-r^p=q refl q refl X = X

-- p=rq^-to-pq=r : {i : Level} {A : Type i} {x y z : A} (p : x ≡ y) (q : z ≡ y)
--                 (r : x ≡ z)
--                 → (p ≡ r ∘ q) → r ^ ∘ p ≡ q
-- p=rq^-to-pq=r refl refl r x = ap (λ p → r ^ ∘ p) x ∘ ass-r (r ^) r refl ∘ ap (λ p' → p' ∘ refl) (inv-o-p r)
