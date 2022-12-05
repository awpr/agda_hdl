open import Categories.Bicartesian using (BicartesianCategory)

module Categories.Gel.Bicartesian {o m ℓ} (𝓒 : BicartesianCategory o m ℓ) where

open BicartesianCategory 𝓒

open import Categories.Gel.Cartesian cartesianCategory public
open import Categories.Gel.Coproducts cartesianCategory coproducts public
