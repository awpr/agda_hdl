open import Categories.Cartesian using (CartesianCategory)
open import Categories.Coproducts using (Coproducts)

module Categories.Gel.Coproducts
    {o m ℓ}
    (𝓒 : CartesianCategory o m ℓ)
    (coproducts : Coproducts (CartesianCategory.𝓤 𝓒))
    where

open CartesianCategory 𝓒 hiding (_⇒_)
open Coproducts coproducts

open import Categories.Gel.Cartesian 𝓒

inj₁ : ∀ {A B} → ⟦ A ⟧ ⟶ ⟦ A ∐ B ⟧
inj₁ f = i₁ ∘ f

inj₂ : ∀ {A B} → ⟦ B ⟧ ⟶ ⟦ A ∐ B ⟧
inj₂ f = i₂ ∘ f

-- Given only a bicartesian (not distributive) category, we can't
-- distribute the "context" inside a coproduct, so when matching
-- coproducts, we can't provide access to that context inside each arm
-- of the match.  As such, the morphism arguments here are _⋆⇒_ rather
-- than _⟨ X ⟩⇒_.
⊎-elim _∥_ : ∀ {A B C} → (⟦ A ⟧ ⋆⇒ ⟦ C ⟧) → (⟦ B ⟧ ⋆⇒ ⟦ C ⟧) → ⟦ A ∐ B ⟧ ⟶ ⟦ C ⟧
(f ∥ g) x = (reify′ f ▽ reify′ g) ∘ x

⊎-elim = _∥_

syntax ⊎-elim (λ x → e₁) (λ y → e₂) e₃ = case e₃ of [ x ⇒ e₁ ∥ y ⇒ e₂ ]
