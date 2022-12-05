{-# OPTIONS --safe #-}

module Categories.BicartesianClosed where

open import Data.Unit using (tt)
open import Level using (Level; _⊔_; suc)

open import Categories.Bicartesian using (Bicartesian; BicartesianCategory; bundle)
open import Categories.Cartesian using (Cartesian)
open import Categories.CartesianClosed using
  ( CartesianClosed
  ; CartesianClosedCategory; bundle
  )
open import Categories.Category using (Category)
open import Categories.Coproducts using (Coproducts)
open import Categories.Distributive using (Distributive; DistributiveCategory; bundle)

record BicartesianClosed {o m ℓ} (𝓒 : Category o m ℓ) : Set (o ⊔ m ⊔ ℓ) where
  open Category 𝓒

  field
    cartesianClosed : CartesianClosed 𝓒
    coproducts : Coproducts 𝓒

  open CartesianClosed cartesianClosed public
  open Coproducts coproducts public

  bicartesian : Bicartesian 𝓒
  bicartesian = record { cartesian = cartesian ; coproducts = coproducts }

  -- Any bicartesian closed category is automatically distributive,
  -- since you can use currying to "partially apply" the case-arms and
  -- "finish applying" them after constructing their copairing.
  distributive : Distributive 𝓒
  distributive = record
    { bicartesian = bicartesian
    ; distʳ = record
        { f⁻¹ = uncurryʳ (curryʳ i₁ ▽ curryʳ i₂)
        }
    }

record BicartesianClosedCategory o m ℓ : Set (suc (o ⊔ m ⊔ ℓ)) where
  constructor bundle
  field
    {𝓤} : Category o m ℓ
    bicartesianClosed : BicartesianClosed 𝓤

  open Category 𝓤 public
  open BicartesianClosed bicartesianClosed public

  cartesianClosedCategory : CartesianClosedCategory o m ℓ
  cartesianClosedCategory = bundle cartesianClosed

  open CartesianClosedCategory cartesianClosedCategory
    using (cartesianCategory; braidedMonoidalCategory; monoidalCategory) public

  bicartesianCategory : BicartesianCategory o m ℓ
  bicartesianCategory = bundle bicartesian

  distributiveCategory : DistributiveCategory o m ℓ
  distributiveCategory = bundle distributive
