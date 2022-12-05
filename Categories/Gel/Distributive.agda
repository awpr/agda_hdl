open import Categories.Distributive using (DistributiveCategory)

module Categories.Gel.Distributive {o m ℓ} (𝓒 : DistributiveCategory o m ℓ) where

open DistributiveCategory 𝓒

import Function

import Categories.Inverse
open Categories.Inverse.In 𝓤 using (RawInverse)
open import Categories.Gel.Cartesian cartesianCategory public
open import Categories.Gel.Coproducts cartesianCategory coproducts
  using (inj₁; inj₂)
  public

⊎-elim _∥_
  : ∀ {A B} {c} {C : Obj → Set c} ⦃ _ : Yoneda C ⦄
  → (⟦ A ⟧ ⇉ C) ⟶ (⟦ B ⟧ ⇉ C) ⇨ ⟦ A ∐ B ⟧ ⇨ C
(f ∥ g) x = wrap (
  (unwrap (_↣_.unwrap (reify f)) ▽ unwrap (_↣_.unwrap (reify g))) ∘
  distʳ .RawInverse.f⁻¹ ∘ (x △ id) )

⊎-elim = _∥_

syntax ⊎-elim (λ x → e₁) (λ y → e₂) e₃ = case e₃ of [ inj₁ x ⇒ e₁ ∥ inj₂ y ⇒ e₂ ]
