{-# OPTIONS --safe #-}

module Categories.BicartesianClosed where

open import Data.Unit using (tt)
open import Level using (Level; _β_; suc)

open import Categories.Bicartesian using (Bicartesian; BicartesianCategory; bundle)
open import Categories.Cartesian using (Cartesian)
open import Categories.CartesianClosed using
  ( CartesianClosed
  ; CartesianClosedCategory; bundle
  )
open import Categories.Category using (Category)
open import Categories.Coproducts using (Coproducts)
open import Categories.Distributive using (Distributive; DistributiveCategory; bundle)

record BicartesianClosed {o m β} (π : Category o m β) : Set (o β m β β) where
  open Category π

  field
    cartesianClosed : CartesianClosed π
    coproducts : Coproducts π

  open CartesianClosed cartesianClosed public
  open Coproducts coproducts public

  bicartesian : Bicartesian π
  bicartesian = record { cartesian = cartesian ; coproducts = coproducts }

  -- Any bicartesian closed category is automatically distributive,
  -- since you can use currying to "partially apply" the case-arms and
  -- "finish applying" them after constructing their copairing.
  distributive : Distributive π
  distributive = record
    { bicartesian = bicartesian
    ; distΚ³ = record
        { fβ»ΒΉ = uncurryΚ³ (curryΚ³ iβ β½ curryΚ³ iβ)
        }
    }

record BicartesianClosedCategory o m β : Set (suc (o β m β β)) where
  constructor bundle
  field
    {π€} : Category o m β
    bicartesianClosed : BicartesianClosed π€

  open Category π€ public
  open BicartesianClosed bicartesianClosed public

  cartesianClosedCategory : CartesianClosedCategory o m β
  cartesianClosedCategory = bundle cartesianClosed

  open CartesianClosedCategory cartesianClosedCategory
    using (cartesianCategory; braidedMonoidalCategory; monoidalCategory) public

  bicartesianCategory : BicartesianCategory o m β
  bicartesianCategory = bundle bicartesian

  distributiveCategory : DistributiveCategory o m β
  distributiveCategory = bundle distributive
