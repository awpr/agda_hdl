{-# OPTIONS --safe #-}

module Categories.Constructions.Opposite where

open import Categories.Category using (Category)

infix 90 _ᵒᵖ
Opposite _ᵒᵖ : ∀ {o m ℓ} → Category o m ℓ → Category o m ℓ
Opposite 𝓒 = record
  { Obj = Obj
  ; _⇒_ = λ A B → B ⇒ A
  ; _≈_ = _≈_
  ; id = id
  ; _∘_ = λ f g → g ∘ f
  ; equiv = equiv
  ; ∘-resp-≈ = λ f₁≈f₂ g₁≈g₂ → ∘-resp-≈ g₁≈g₂ f₁≈f₂
  ; ∘-idˡ = ∘-idʳ
  ; ∘-idʳ = ∘-idˡ
  ; ∘-assocˡ = ∘-assocʳ
  }
  where open Category 𝓒

_ᵒᵖ = Opposite
