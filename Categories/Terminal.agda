{-# OPTIONS --safe #-}

module Categories.Terminal where

open import Level using (_⊔_)

open import Categories.Category

module _ {o m ℓ} (𝓒 : Category o m ℓ) where
  record TerminalObject : Set (o ⊔ m ⊔ ℓ) where
    open Category 𝓒
    field
      ⋆ : Obj
      ε : ∀ {A} → A ⇒ ⋆
      ε-unique : ∀ {A} {f : A ⇒ ⋆} → f ≈ ε
