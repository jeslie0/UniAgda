{-# OPTIONS --without-K #-}
module UniAgda.bicategories.bicategory where

open import UniAgda.core.CORE public

record prebicategory {i₁ i₂ i₃ : Level} : Type (lsuc (i₁ ⊔ i₂ ⊔ i₃)) where
  no-eta-equality


  field
    0-cell : Type i₁

    1-cell : (a b : 0-cell)
             → Type i₂

    2-cell : {a b : 0-cell}
             (f g : 1-cell a b)
             → Type i₃

    id₁ : {a : 0-cell}
          → 1-cell a a

    _·_  : {a b c : 0-cell} →
           1-cell a b → 1-cell b c → 1-cell a c

    id₂ : {a b : 0-cell} {f : 1-cell a b}
          → 2-cell f f

    _⊗_ : {a b : 0-cell} {f g h : 1-cell a b}
          (θ : 2-cell f g) (γ : 2-cell g h)
          → 2-cell f h

    _◃_ : {a b c : 0-cell} {g h : 1-cell b c}
          (f : 1-cell a b) (θ : 2-cell g h)
          → 2-cell (f · g) (f · h)

    _▹_ : {a b c : 0-cell} {f g : 1-cell a b}
          (θ : 2-cell f g) (h : 1-cell b c)
          → 2-cell (f · h) (g · h)

    l-λ : {a b : 0-cell}
          (f : 1-cell a b)
          → 2-cell (id₁ · f) f --fix name

    l-λ^ : {a b : 0-cell}
           (f : 1-cell a b)
           → 2-cell f (id₁ · f)

    r-ρ : {a b : 0-cell}
          (f : 1-cell a b)
          → 2-cell (f · id₁) f

    r-ρ^ : {a b : 0-cell}
           (f : 1-cell a b)
           → 2-cell f (f · id₁)

    α : {a b c d : 0-cell}
          (f : 1-cell a b) (g : 1-cell b c) (h : 1-cell c d)
          → 2-cell (f · (g · h)) ((f · g) · h)

    α^ : {a b c d : 0-cell}
          (f : 1-cell a b) (g : 1-cell b c) (h : 1-cell c d)
          → 2-cell ((f · g) · h) (f · (g · h))


    bicat-ax1i : {a b : 0-cell} {g : 1-cell a b}
                 (f : 1-cell a b) (θ : 2-cell f g)
                 → id₂ ⊗ θ ≡ θ

    bicat-ax1ii : {a b : 0-cell} {f : 1-cell a b}
                  (g : 1-cell a b) (θ : 2-cell f g)
                 → θ ⊗ id₂ ≡ θ

    bicat-ax1iii : {a b : 0-cell} {f g h k : 1-cell a b}
                   (θ : 2-cell f g) (γ : 2-cell g h) (τ : 2-cell h k)
                   → θ ⊗ (γ ⊗ τ) ≡ (θ ⊗ γ) ⊗ τ

    bicat-ax2i : {a b c : 0-cell}
                 (f : 1-cell a b) (g : 1-cell b c)
                 → f ◃ (id₂ {b} {c} {g}) ≡ id₂ {a} {c} {f · g}

    bicat-ax2ii : {a b c : 0-cell} {g₁ g₂ g₃ : 1-cell b c}
                  (f : 1-cell a b) (θ : 2-cell g₁ g₂) (γ : 2-cell g₂ g₃)
                  → f ◃ (θ ⊗ γ) ≡ (f ◃ θ) ⊗ (f ◃ γ)

    bicat-ax3i : {a b c : 0-cell}
                 (f : 1-cell a b) (g : 1-cell b c)
                 → (id₂ {a} {b} {f}) ▹ g ≡ id₂ {a} {c} {f · g}

    bicat-ax3ii : {a b c : 0-cell} {f₁ f₂ f₃ : 1-cell a b}
                  (θ : 2-cell f₁ f₂) (γ : 2-cell f₂ f₃) (g : 1-cell b c)
                  → (θ ⊗ γ) ▹ g ≡ (θ ▹ g) ⊗ (γ ▹ g)

    bicat-ax4 : {a b : 0-cell} {f g : 1-cell a b}
                (θ : 2-cell f g)
                → (id₁ ◃ θ) ⊗ (l-λ g) ≡ (l-λ f) ⊗ θ

    bicat-ax5 : {a b : 0-cell} {f g : 1-cell a b}
                (θ : 2-cell f g)
                → (θ ▹ id₁) ⊗ (r-ρ g) ≡ (r-ρ f) ⊗ θ

    bicat-ax6 : {a b c d : 0-cell} {h k : 1-cell c d}
                (f : 1-cell a b) (g : 1-cell b c) (θ : 2-cell h k)
                → (f ◃ (g ◃ θ)) ⊗ (α f g k) ≡ (α f g h) ⊗ ((f · g) ◃ θ)

    bicat-ax7 : {a b c d : 0-cell} {g h : 1-cell b c}
                (f : 1-cell a b) (θ : 2-cell g h) (k : 1-cell c d)
                → (f ◃ (θ ▹ k)) ⊗ (α f h k) ≡ (α f g k) ⊗ ((f ◃ θ) ▹ k)

    bicat-ax8 : {a b c d : 0-cell} {f g : 1-cell a b}
                (θ : 2-cell f g) (h : 1-cell b c) (k : 1-cell c d)
                → (θ ▹ (h · k)) ⊗ (α g h k) ≡ (α f h k) ⊗ ((θ ▹ h) ▹ k)

    bicat-ax9i : {a b : 0-cell} {f : 1-cell a b}
                → (l-λ f) ⊗ (l-λ^ f) ≡ id₂

    bicat-ax9ii : {a b : 0-cell} {f : 1-cell a b}
                  → (l-λ^ f) ⊗ (l-λ f) ≡ id₂

    bicat-ax10i : {a b : 0-cell} {f : 1-cell a b}
                  → (r-ρ f) ⊗ (r-ρ^ f) ≡ id₂

    bicat-ax10ii : {a b : 0-cell} {f : 1-cell a b}
                   → (r-ρ^ f) ⊗ (r-ρ f) ≡ id₂

    bicat-ax11i : {a b c d : 0-cell} {f : 1-cell a b} {g : 1-cell b c} {h : 1-cell c d}
                  → (α f g h) ⊗ (α^ f g h) ≡ id₂

    bicat-ax11ii : {a b c d : 0-cell} {f : 1-cell a b} {g : 1-cell b c} {h : 1-cell c d}
                  → (α^ f g h) ⊗ (α f g h) ≡ id₂

    bicat-ax11 : {a b c : 0-cell} {f g : 1-cell a b} {h k : 1-cell b c} (θ : 2-cell f g)
                 (γ : 2-cell h k)
                 → (θ ▹ h) ⊗ (g ◃ γ) ≡ (f ◃ γ) ⊗ (θ ▹ k)

    unity : {a b c : 0-cell}
            (f : 1-cell a b) (g : 1-cell b c)
            → (α f id₁ g) ⊗ ((r-ρ f) ▹ g) ≡ f ◃ (l-λ g)

    pentagon : {a b c d e : 0-cell} {f : 1-cell a b} {g : 1-cell b c} {h : 1-cell c d} {k : 1-cell d e}
               → (α f g (h · k)) ⊗ (α (f · g) h k) ≡ (f ◃ (α g h k)) ⊗ ((α f (g · h) k) ⊗ ((α f g h) ▹ k))

    2-cells-are-sets : {a b : 0-cell}
                       (f g : 1-cell a b)
                       → isSet (2-cell f g)

-- open prebicategory public

  infixr 20 _⊗_
  infixl 30 _◃_
  infixr 30 _▹_
  infixr 20 _·_

  ass-to-middle : {a b : 0-cell} {f g h k l : 1-cell a b}
                  (θ : 2-cell f g) (γ : 2-cell g h) (ϕ : 2-cell h k) (ψ : 2-cell k l)
                  → (θ ⊗ γ) ⊗ (ϕ ⊗ ψ) ≡ θ ⊗ (γ ⊗ ϕ) ⊗ ψ
  ass-to-middle θ γ ϕ ψ = (bicat-ax1iii (θ ⊗ γ) ϕ ψ ∘ transport (λ Z → Z ⊗ ψ ≡ (θ ⊗ γ ⊗ ϕ) ⊗ ψ) (bicat-ax1iii θ γ ϕ) refl) ∘ bicat-ax1iii θ (γ ⊗ ϕ) ψ ^


  hcomp : {a b c : 0-cell} {f₁ g₁ : 1-cell a b} {f₂ g₂ : 1-cell b c}
          (θ : 2-cell f₁ g₁) (γ : 2-cell f₂ g₂)
          → 2-cell (f₁ · f₂) (g₁ · g₂)
  hcomp {a} {b} {c} {f₁} {g₁} {f₂} {g₂} θ γ =
    (θ ▹ f₂) ⊗ ((g₁ ◃ γ))
  _h·_ = hcomp

  hcomp' : {a b c : 0-cell} {f₁ g₁ : 1-cell a b} {f₂ g₂ : 1-cell b c}
           (θ : 2-cell f₁ g₁) (γ : 2-cell f₂ g₂)
           → 2-cell (f₁ · f₂) (g₁ · g₂)
  hcomp' {a} {b} {c} {f₁} {g₁} {f₂} {g₂} θ γ =
    (f₁ ◃ γ) ⊗ (θ ▹ g₂)

  hcomp-eq : {a b c : 0-cell} {f₁ g₁ : 1-cell a b} {f₂ g₂ : 1-cell b c}
             (θ : 2-cell f₁ g₁) (γ : 2-cell f₂ g₂)
             → hcomp θ γ ≡ hcomp' θ γ
  hcomp-eq θ γ = bicat-ax11 θ γ

  interchange : {a b c : 0-cell} {f₁ g₁ h₁ : 1-cell a b} {f₂ g₂ h₂ : 1-cell b c}
                (θ₁ : 2-cell f₁ g₁) (θ₂ : 2-cell f₂ g₂) (γ₁ : 2-cell g₁ h₁) (γ₂ : 2-cell g₂ h₂)
                → (θ₁ h· θ₂) ⊗ (γ₁ h· γ₂) ≡ ((θ₁ ⊗ γ₁) h· (θ₂ ⊗ γ₂))
  interchange {a} {b} {c} {f₁} {g₁} {h₁} {f₂} {g₂} {h₂} θ₁ θ₂ γ₁ γ₂ =
    (bicat-ax11 (θ₁ ⊗ γ₁) (θ₂ ⊗ γ₂) ∘
      transport (λ Z → Z ⊗ (θ₁ ⊗ γ₁) ▹ h₂ ≡ (θ₁ h· θ₂) ⊗ (γ₁ h· γ₂)) (bicat-ax2ii f₁ θ₂ γ₂ ^)
        (transport (λ Z → (f₁ ◃ θ₂ ⊗ f₁ ◃ γ₂) ⊗ Z ≡ (θ₁ h· θ₂) ⊗ (γ₁ h· γ₂)) (bicat-ax3ii θ₁ γ₁ h₂ ^)
          (ass-to-middle (f₁ ◃ θ₂) (f₁ ◃ γ₂) (θ₁ ▹ h₂) (γ₁ ▹ h₂) ∘
          transport (λ Z → f₁ ◃ θ₂ ⊗ (Z) ⊗ γ₁ ▹ h₂ ≡ (θ₁ h· θ₂) ⊗ (γ₁ h· γ₂)) (bicat-ax11 θ₁ γ₂)
            (ass-to-middle (f₁ ◃ θ₂) (θ₁ ▹ g₂) (g₁ ◃ γ₂) (γ₁ ▹ h₂) ^ ∘ transport (λ Z → (Z) ⊗ g₁ ◃ γ₂ ⊗ γ₁ ▹ h₂ ≡ (θ₁ h· θ₂) ⊗ (γ₁ h· γ₂)) (bicat-ax11 θ₁ θ₂)
              (transport (λ Z → (θ₁ ▹ f₂ ⊗ g₁ ◃ θ₂) ⊗ Z ≡ (θ₁ h· θ₂) ⊗ (γ₁ h· γ₂)) (bicat-ax11 γ₁ γ₂) refl))))) ^
        

  record int-adj (X Y : 0-cell) : Type (lsuc (i₁ ⊔ i₂ ⊔ i₃)) where
    eta-equality
    field
      left : 1-cell X Y
      right : 1-cell Y X
      η : 2-cell (id₁ {X}) (left · right)

      ε : 2-cell (right · left) (id₁)

      left-triangle : let f = left
                          g = right
                      in (η ▹ f) ⊗ ((α^ f g f) ⊗ ((f ◃ ε) ⊗ (r-ρ f))) ≡ l-λ f

      right-triangle : let f = left
                           g = right
                       in (g ◃ η) ⊗ ((α g f g) ⊗ ((ε ▹ g) ⊗ (l-λ g))) ≡ r-ρ g

  open int-adj public

  left-to-right-mate : (X₀ Y₀ X₁ Y₁ : 0-cell) (adj₀ : int-adj X₀ Y₀) (adj₁ : int-adj X₁ Y₁) (a : 1-cell X₀ X₁) (b : 1-cell Y₀ Y₁) (w : 2-cell (a · (left adj₁)) (left adj₀ · b))
                       → 2-cell (right adj₀ · a) (b · right adj₁)
  left-to-right-mate X₀ Y₀ X₁ Y₁ record { left = f₀ ; right = g₀ ; η = η₀ ; ε = ε₀ ; left-triangle = left-triangle₀ ; right-triangle = right-triangle₀ } record { left = f₁ ; right = g₁ ; η = η₁ ; ε = ε₁ ; left-triangle = left-triangle₁ ; right-triangle = right-triangle₁ } a b w = 
    r-ρ^ (g₀ · a) ⊗ (((g₀ · a) ◃ η₁) ⊗ (((α^ g₀ a (f₁ · g₁) ⊗ ((g₀ ◃ (α a f₁ g₁)) ⊗ ((g₀ ◃ (w ▹ g₁)) ⊗ ((g₀ ◃ (α^ f₀ b g₁)) ⊗ α g₀ f₀ (b · g₁))))) ⊗ (ε₀ ▹ (b · g₁))) ⊗ (l-λ (b · g₁))))

  right-to-left-mate : (X₀ Y₀ X₁ Y₁ : 0-cell) (adj₀ : int-adj X₀ Y₀) (adj₁ : int-adj X₁ Y₁) (a : 1-cell X₀ X₁) (b : 1-cell Y₀ Y₁) (ν : 2-cell (right adj₀ · a) (b · right adj₁))
                     → 2-cell (a · left adj₁) (left adj₀ · b)
  right-to-left-mate X₀ Y₀ X₁ Y₁ record { left = f₀ ; right = g₀ ; η = η₀ ; ε = ε₀ ; left-triangle = left-triangle₀ ; right-triangle = right-triangle₀ } record { left = f₁ ; right = g₁ ; η = η₁ ; ε = ε₁ ; left-triangle = left-triangle₁ ; right-triangle = right-triangle₁ } a b ν = l-λ^ (a · f₁) ⊗ (η₀ ▹ (a · f₁) ⊗ (α^ f₀ g₀ (a · f₁) ⊗ (f₀ ◃ (α g₀ a f₁) ⊗ ( f₀ ◃ (ν ▹ f₁) ⊗ (f₀ ◃ (α^ b g₁ f₁) ⊗ (α f₀ b (g₁ · f₁) ⊗ ((f₀ · b) ◃ ε₁ ⊗ r-ρ (f₀ · b))))))))

  left-to-right-to-left-Id : (X₀ Y₀ X₁ Y₁ : 0-cell) (adj₀ : int-adj X₀ Y₀) (adj₁ : int-adj X₁ Y₁) (a : 1-cell X₀ X₁) (b : 1-cell Y₀ Y₁) (w : 2-cell (a · (left adj₁)) (left adj₀ · b))
                           → right-to-left-mate X₀ Y₀ X₁ Y₁ adj₀ adj₁ a b (left-to-right-mate X₀ Y₀ X₁ Y₁ adj₀ adj₁ a b w) ≡ w
  left-to-right-to-left-Id X₀ Y₀ X₁ Y₁ record { left = f₀ ; right = g₀ ; η = η₀ ; ε = ε₀ ; left-triangle = left-triangle₀ ; right-triangle = right-triangle₀ } record { left = f₁ ; right = g₁ ; η = η₁ ; ε = ε₁ ; left-triangle = left-triangle₁ ; right-triangle = right-triangle₁ } a b w = {!-m!}


  right-to-left-to-right-Id : (X₀ Y₀ X₁ Y₁ : 0-cell) (adj₀ : int-adj X₀ Y₀) (adj₁ : int-adj X₁ Y₁) (a : 1-cell X₀ X₁) (b : 1-cell Y₀ Y₁) (ν : 2-cell (right adj₀ · a) (b · right adj₁))
                            → left-to-right-mate X₀ Y₀ X₁ Y₁ adj₀ adj₁ a b (right-to-left-mate X₀ Y₀ X₁ Y₁ adj₀ adj₁ a b ν) ≡ ν
  right-to-left-to-right-Id X₀ Y₀ X₁ Y₁ record { left = f₀ ; right = g₀ ; η = η₀ ; ε = ε₀ ; left-triangle = left-triangle₀ ; right-triangle = right-triangle₀ } record { left = f₁ ; right = g₁ ; η = η₁ ; ε = ε₁ ; left-triangle = left-triangle₁ ; right-triangle = right-triangle₁ } a b ν = {!!}
