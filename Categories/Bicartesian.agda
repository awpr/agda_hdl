{-# OPTIONS --safe #-}

module Categories.Bicartesian where

open import Level using (Level; _⊔_; suc)

open import Categories.Category using (Category)
open import Categories.Cartesian using (Cartesian; CartesianCategory; bundle)
open import Categories.Coproducts using (Coproducts)
open import Categories.Monoidal using (MonoidalCategory; bundle)

record Bicartesian {o m ℓ} (𝓒 : Category o m ℓ) : Set (o ⊔ m ⊔ ℓ) where
  open Category 𝓒

  field
    cartesian : Cartesian 𝓒
    coproducts : Coproducts 𝓒

  open Cartesian cartesian public
  open Coproducts coproducts public

  factorˡ : ∀ {A B C} → A × B ∐ A × C ⇒ A × (B ∐ C)
  factorˡ = p₁ △ i₁ ∘ p₂ ▽ p₁ △ i₂ ∘ p₂

  factorʳ : ∀ {A B C} → A × B ∐ C × B ⇒ (A ∐ C) × B
  factorʳ = i₁ ∘ p₁ △ p₂ ▽ i₂ ∘ p₁ △ p₂

record BicartesianCategory o m ℓ : Set (suc (o ⊔ m ⊔ ℓ)) where
  constructor bundle
  field
    {𝓤} : Category o m ℓ
    bicartesian : Bicartesian 𝓤

  open Category 𝓤 public
  open Bicartesian bicartesian public

  cartesianCategory : CartesianCategory o m ℓ
  cartesianCategory = bundle cartesian

  monoidalCategory : MonoidalCategory o m ℓ
  monoidalCategory = bundle monoidal
