{-# OPTIONS --safe #-}

module Categories.Constructions.Product where

open import Data.Product using (_×_; _,_)

open import Categories.Category using (Category)

-- ⨂ is \Ox
infixr 40 _⨂_
_⨂_ : ∀ {o₁ m₁ ℓ₁ o₂ m₂ ℓ₂} → Category o₁ m₁ ℓ₁ → Category o₂ m₂ ℓ₂ → Category _ _ _
𝓒 ⨂ 𝓓 = record
  { Obj = 𝓒.Obj × 𝓓.Obj
  ; _⇒_ = λ (A₁ , A₂) (B₁ , B₂) → A₁ 𝓒.⇒ B₁ × A₂ 𝓓.⇒ B₂
  ; _≈_ = λ (f₁ , f₂) (g₁ , g₂) → f₁ 𝓒.≈ g₁ × f₂ 𝓓.≈ g₂
  ; id = 𝓒.id , 𝓓.id
  ; _∘_ = λ (f₁ , f₂) (g₁ , g₂) → f₁ 𝓒.∘ g₁ , f₂ 𝓓.∘ g₂

  ; equiv = record
      { refl = 𝓒.≈.refl , 𝓓.≈.refl
      ; sym = λ (f₁≈g₁ , f₂≈g₂) → 𝓒.≈.sym f₁≈g₁ , 𝓓.≈.sym f₂≈g₂
      ; trans = λ (f₁≈g₁ , f₂≈g₂) (g₁≈h₁ , g₂≈h₂) →
          𝓒.≈.trans f₁≈g₁ g₁≈h₁ , 𝓓.≈.trans f₂≈g₂ g₂≈h₂
      }

  ; ∘-resp-≈ = λ (f₁₁≈f₁₂ , f₂₁≈f₂₂) (g₁₁≈g₁₂ , g₂₁≈g₂₂) →
       𝓒.∘-resp-≈ f₁₁≈f₁₂ g₁₁≈g₁₂ , 𝓓.∘-resp-≈ f₂₁≈f₂₂ g₂₁≈g₂₂

  ; ∘-idˡ = 𝓒.∘-idˡ , 𝓓.∘-idˡ
  ; ∘-idʳ = 𝓒.∘-idʳ , 𝓓.∘-idʳ
  ; ∘-assocˡ = 𝓒.∘-assocˡ , 𝓓.∘-assocˡ
  }
  where
    module 𝓒 = Category 𝓒
    module 𝓓 = Category 𝓓
