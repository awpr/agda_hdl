{-# OPTIONS --safe #-}

module Categories.Braided where

open import Level using (Level; _⊔_; suc)

open import Categories.Bifunctor using (Flip)
open import Categories.Category using (Category)
open import Categories.Category.Functors using (Fun; natIso)
import Categories.Functor
open Categories.Functor.FunctorOperators
open import Categories.Monoidal using (Monoidal; MonoidalCategory; bundle)
open import Categories.NaturalTransformation using (wrapNT)
open import Categories.Inverse using (_[_≅_])

-- Design philosophy note: in the case of symmetric monoidal
-- categories, we have a tall tower of abstractions that each augment
-- the previous with some extra structure.  In different
-- circumstances, we'll want to parameterize over different amounts of
-- that structure: we might already have a particular monoidal
-- structure in mind and want to name just the additional structure of
-- "braidedness", or we might want to parameterize something over an
-- entire category equipped with braided monoidal structure.
--
-- To accommodate this, we'll provide the following variants:
--
-- * The present additional property on its own, parameterized by
--   everything below in bundled form: `Braided` structure given a
--   particular `MonoidalCategory`.
-- * All of the relevant structure down to the underlying category:
--   `BraidedMonoidal` parameterized by a `Category`, providing both
--   the monoidal structure and the braided structure atop it.
-- * Everything including the underlying category wrapped into one
--   bundle: `BraidedMonoidalCategory`.
--
-- As a general rule, a record opens-public its fields but not its
-- parameters.

-- A particular `MonoidalCategory` is braided w.r.t. its monoidal structure.
record Braided {o m ℓ} (𝓒 : MonoidalCategory o m ℓ) : Set (o ⊔ m ⊔ ℓ) where
  open MonoidalCategory 𝓒
  open Categories.Inverse.In 𝓤

  field
    -- Trying out a different approach to these structure records:
    -- even though the structure can be more succinctly stated as "a
    -- natural isomorphism", include the components directly in terms
    -- of simpler categories to reduce work spent on unifying large
    -- constructed categories.  Then, provide the succinct version as
    -- a binding in the record module.  If this turns out well, TODO
    -- change other records to do the same.
    braiding : ∀ {A B} → A ⊗ B ≅ B ⊗ A
    naturality
      : ∀ {A₁ A₂ B₁ B₂ f}
      → (braiding {A₁} {A₂} ¹) ∘ -⊗- ₁ f ≈
          Flip -⊗- ₁ f ∘ (braiding {B₁} {B₂} ¹)

  braidingNatIso : Fun _ _ [ -⊗- ≅ Flip -⊗- ]
  braidingNatIso = natIso _ _
    (wrapNT record { α = braiding ¹ ; naturality = naturality })
    (isoToInverse braiding)

  braid : ∀ {A B} → A ⊗ B ⇒ B ⊗ A
  braid = braiding ¹

  unbraid : ∀ {A B} → A ⊗ B ⇒ B ⊗ A
  unbraid = braiding ⁻¹

-- A particular `Category` has braided monoidal structure.
record BraidedMonoidal {o m ℓ} (𝓒 : Category o m ℓ) : Set (o ⊔ m ⊔ ℓ) where
  constructor bundle
  field
    {monoidal} : Monoidal 𝓒
    braided : Braided (bundle monoidal)

  open Monoidal monoidal public
  open Braided braided public

-- Some `Category` along with braided monoidal structure on it.
record BraidedMonoidalCategory (o m ℓ : Level) : Set (suc (o ⊔ m ⊔ ℓ)) where
  constructor bundle
  field
    {𝓤} : Category o m ℓ
    braided : BraidedMonoidal 𝓤

  open Category 𝓤 public
  open BraidedMonoidal braided public
