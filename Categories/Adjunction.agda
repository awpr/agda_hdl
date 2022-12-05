{-# OPTIONS --safe #-}
module Categories.Adjunction where

open import Level using (_⊔_)

open import Categories.Category using (Category)
open import Categories.Functor using (Functor; module FunctorOperators)

-- ⊣ is \-|.
record _⊣_
    {o₁ m₁ ℓ₁ o₂ m₂ ℓ₂}
    {𝓒 : Category o₁ m₁ ℓ₁}
    {𝓓 : Category o₂ m₂ ℓ₂}
    (L : Functor 𝓒 𝓓)
    (R : Functor 𝓓 𝓒)
    : Set (o₁ ⊔ m₁ ⊔ ℓ₁ ⊔ o₂ ⊔ m₂ ⊔ ℓ₂) where
  private module 𝓒 = Category 𝓒
  private module 𝓓 = Category 𝓓
  open FunctorOperators using (_₀_)

  field
    left-adjunct : ∀ {A B} → A 𝓒.⇒ R ₀ B → L ₀ A 𝓓.⇒ B
    right-adjunct : ∀ {A B} → L ₀ A 𝓓.⇒ B → A 𝓒.⇒ R ₀ B

    left-inverse : ∀ {A B} {f : L ₀ A 𝓓.⇒ B} → left-adjunct (right-adjunct f) 𝓓.≈ f
    right-inverse : ∀ {A B} {f : A 𝓒.⇒ R ₀ B} → right-adjunct (left-adjunct f) 𝓒.≈ f

    -- TODO: naturality equivalences

  unit : ∀ {A} → A 𝓒.⇒ R ₀ (L ₀ A)
  unit = right-adjunct 𝓓.id

  counit : ∀ {A} → L ₀ (R ₀ A) 𝓓.⇒ A
  counit = left-adjunct 𝓒.id
