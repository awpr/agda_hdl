open import Categories.BicartesianClosed using (BicartesianClosedCategory)

module Categories.Gel.BicartesianClosed
    {o m ℓ} (𝓒 : BicartesianClosedCategory o m ℓ)
    where

open BicartesianClosedCategory 𝓒

open import Categories.Gel.CartesianClosed cartesianClosedCategory public
open import Categories.Gel.Coproducts cartesianCategory coproducts
  hiding (⊎-elim; _∥_) public
open import Categories.Gel.Distributive distributiveCategory public using (⊎-elim; _∥_)

-- Internal (to the category) version of _∥_: produces the copairing
-- of two exponentials as an exponential, rather than the copairing of
-- two morphisms as a morphism.
_⟨∥⟩_ : ∀ {A B C} → ⟦ A ↝ C ⟧ ⟶ ⟦ B ↝ C ⟧ ⇨ ⟦ A ∐ B ↝ C ⟧
f ⟨∥⟩ g = flip (flip f ▽ flip g)
