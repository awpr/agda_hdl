{-# OPTIONS --safe #-}

module Categories.Coproducts where

open import Level using (_⊔_)

open import Categories.Category using (Category)

record Coproducts {o m ℓ} (𝓒 : Category o m ℓ) : Set (o ⊔ m ⊔ ℓ) where
  open Category 𝓒

  -- less than infixr 40 _×_ _⊗_; greater than infixr 30 _↝_
  infixr 35 _∐_ -- ∐ is \coprod

  -- less than infixr 20 _△_
  infixr 15 _▽_

  field
    _∐_ : (A B : Obj) → Obj
    ⊥ : Obj

    ∃! : ∀ {A} → ⊥ ⇒ A
    i₁ : ∀ {A B} → A ⇒ A ∐ B
    i₂ : ∀ {A B} → B ⇒ A ∐ B
    _▽_ : ∀ {A B C} → A ⇒ C → B ⇒ C → A ∐ B ⇒ C

    ▽-resp-≈
      : ∀ {A B C} {f₁ f₂ : A ⇒ C} {g₁ g₂ : B ⇒ C}
      → f₁ ≈ f₂ → g₁ ≈ g₂ → f₁ ▽ g₁ ≈ f₂ ▽ g₂

  swap⊎ : ∀ {A B} → A ∐ B ⇒ B ∐ A
  swap⊎ = i₂ ▽ i₁

  bimap⊎ : ∀ {A B C D} → A ⇒ B → C ⇒ D → A ∐ C ⇒ B ∐ D
  bimap⊎ f g = i₁ ∘ f ▽ i₂ ∘ g
