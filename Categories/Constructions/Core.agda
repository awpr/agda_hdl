{-# OPTIONS --safe #-}

open import Categories.Category using (Category; _[_≈_])

module Categories.Constructions.Core {o m ℓ} (𝓒 : Category o m ℓ) where

open import Level using (_⊔_)
open import Relation.Binary.Structures using (IsEquivalence)

import Categories.Inverse

open Category 𝓒 hiding (_≈_)
open Categories.Inverse.In 𝓒

record _≈_ {A B : Obj} (f g : A ≅ B) : Set ℓ where
  field
    _¹ : 𝓒 [ f ¹ ≈ g ¹ ]
    _⁻¹ : 𝓒 [ f ⁻¹ ≈ g ⁻¹ ]

open _≈_ public

≈-refl : ∀ {A B} {f : A ≅ B} → f ≈ f
≈-refl = record { _¹ = ≈.refl ; _⁻¹ = ≈.refl }

≈-sym : ∀ {A B} {f g : A ≅ B} → f ≈ g → g ≈ f
≈-sym f≈g = record { _¹ = ≈.sym (f≈g ¹) ; _⁻¹ = ≈.sym (f≈g ⁻¹) }

≈-trans : ∀ {A B} {f g h : A ≅ B} → f ≈ g → g ≈ h → f ≈ h
≈-trans f≈g g≈h = record
  { _¹ = ≈.trans (f≈g ¹) (g≈h ¹)
  ; _⁻¹ = ≈.trans (f≈g ⁻¹) (g≈h ⁻¹)
  }

≈-equiv : ∀ {A B} → IsEquivalence (_≈_ {A} {B})
≈-equiv = record { refl = ≈-refl ; sym = ≈-sym ; trans = ≈-trans }

Core : Category o (m ⊔ ℓ) ℓ
Core = record
  { Obj = Obj
  ; _⇒_ = _≅_
  ; _≈_ = _≈_
  ; id = ≅-refl
  ; _∘_ = λ f g → ≅-trans g f
  ; equiv = ≈-equiv
  ; ∘-resp-≈ = λ f₁≈f₂ g₁≈g₂ → record
      { _¹ = ∘-resp-≈ (f₁≈f₂ ¹) (g₁≈g₂ ¹)
      ; _⁻¹ = ∘-resp-≈ (g₁≈g₂ ⁻¹) (f₁≈f₂ ⁻¹)
      }
  ; ∘-idˡ = record { _¹ = ∘-idˡ ; _⁻¹ = ∘-idʳ }
  ; ∘-idʳ = record { _¹ = ∘-idʳ ; _⁻¹ = ∘-idˡ }
  ; ∘-assocˡ = record { _¹ = ∘-assocˡ ; _⁻¹ = ∘-assocʳ }
  }
