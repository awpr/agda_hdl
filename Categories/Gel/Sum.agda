open import Categories.Distributive using (DistributiveCategory)

module Categories.Gel.Sum {o m ℓ} (𝓒 : DistributiveCategory o m ℓ) where

open import Level using (Level)

open import Categories.Gel.Distributive 𝓒
open DistributiveCategory 𝓒

private
  variable
    a b c : Level
    A : Obj → Set a
    B : Obj → Set b
    C : Obj → Set c

infixr 30 _⊎_ -- TODO: 30 is arbitrary, think it through
record _⊎_
    (A : Obj → Set a) ⦃ _ : Yoneda A ⦄
    (B : Obj → Set b) ⦃ _ : Yoneda B ⦄
    (X : Obj)
    : Set m where
  field
    unwrap : ⟦ Rep A ∐ Rep B ⟧ X

instance
  yoneda⊎ : ⦃ _ : Yoneda A ⦄ ⦃ _ : Yoneda B ⦄ → Yoneda (A ⊎ B)
  yoneda⊎ = record { wrap = λ x → record { unwrap = x } ; unwrap = _⊎_.unwrap }

  module _ ⦃ _ : Yoneda A ⦄ ⦃ _ : Yoneda B ⦄ where
    open Yoneda (yoneda⊎ {A = A} {B = B}) public using () renaming (presheaf to presheaf⊎)


left : ⦃ _ : Yoneda A ⦄ ⦃ _ : Yoneda B ⦄ → A ⟶ A ⊎ B
left x = record { unwrap = inj₁ (unwrap x) }

right : ⦃ _ : Yoneda A ⦄ ⦃ _ : Yoneda B ⦄ → B ⟶ A ⊎ B
right x = record { unwrap = inj₂ (unwrap x) }

either : ⦃ _ : Yoneda A ⦄ ⦃ _ : Yoneda B ⦄ ⦃ _ : Yoneda C ⦄ → (A ⇉ C) ⟶ (B ⇉ C) ⇨ A ⊎ B ⇨ C
either f g xy = case unwrap xy of [ inj₁ x ⇒ f (wrap x) ∥ inj₂ y ⇒ g (wrap y) ]
