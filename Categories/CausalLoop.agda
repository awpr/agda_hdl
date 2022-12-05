module Categories.CausalLoop where

open import Level using (_⊔_)

open import Categories.Monoidal using (MonoidalCategory)

record Causal {o m ℓ} (𝓒 : MonoidalCategory o m ℓ) : Set (o ⊔ m) where
  open MonoidalCategory 𝓒
  field
    loop
      : ∀ {A B S : Obj}
      → 𝟏 ⇒ S
      → S ⊗ A ⇒ S ⊗ B
      → A ⇒ B
