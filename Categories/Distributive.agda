{-# OPTIONS --safe #-}

module Categories.Distributive where

open import Data.Unit using (tt)
open import Level using (suc; _⊔_)

open import Categories.Bicartesian using (Bicartesian)
open import Categories.Cartesian using (CartesianCategory; bundle)
open import Categories.Category using (Category)
import Categories.Inverse
open import Categories.NaturalTransformation using (α)

record Distributive {o m ℓ} (𝓒 : Category o m ℓ) : Set (o ⊔ m ⊔ ℓ) where
  open Category 𝓒
  open Categories.Inverse.In 𝓒

  field
    bicartesian : Bicartesian 𝓒

  open Bicartesian bicartesian public

  field
    distʳ : ∀ {A B C} → RawInverse (factorʳ {A} {B} {C})

  distˡ : ∀ {A B C} → RawInverse (factorˡ {A} {B} {C})
  distˡ = record
    { f⁻¹ = bimap⊎ (swap .α) (swap .α) ∘ distʳ .RawInverse.f⁻¹ ∘ swap .α
    }

record DistributiveCategory o m ℓ : Set (suc (o ⊔ m ⊔ ℓ)) where
  constructor bundle
  field
    {𝓤} : Category o m ℓ
    distributive : Distributive 𝓤

  open Category 𝓤 public
  open Distributive distributive public

  cartesianCategory : CartesianCategory o m ℓ
  cartesianCategory = bundle cartesian

  open CartesianCategory cartesianCategory
    using (monoidalCategory)
    public
