{-# OPTIONS --safe #-}

module Categories.Bicartesian where

open import Level using (Level; _β_; suc)

open import Categories.Category using (Category)
open import Categories.Cartesian using (Cartesian; CartesianCategory; bundle)
open import Categories.Coproducts using (Coproducts)
open import Categories.Monoidal using (MonoidalCategory; bundle)

record Bicartesian {o m β} (π : Category o m β) : Set (o β m β β) where
  open Category π

  field
    cartesian : Cartesian π
    coproducts : Coproducts π

  open Cartesian cartesian public
  open Coproducts coproducts public

  factorΛ‘ : β {A B C} β A Γ B β A Γ C β A Γ (B β C)
  factorΛ‘ = pβ β³ iβ β pβ β½ pβ β³ iβ β pβ

  factorΚ³ : β {A B C} β A Γ B β C Γ B β (A β C) Γ B
  factorΚ³ = iβ β pβ β³ pβ β½ iβ β pβ β³ pβ

record BicartesianCategory o m β : Set (suc (o β m β β)) where
  constructor bundle
  field
    {π€} : Category o m β
    bicartesian : Bicartesian π€

  open Category π€ public
  open Bicartesian bicartesian public

  cartesianCategory : CartesianCategory o m β
  cartesianCategory = bundle cartesian

  monoidalCategory : MonoidalCategory o m β
  monoidalCategory = bundle monoidal
