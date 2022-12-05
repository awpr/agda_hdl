open import Categories.Distributive using (DistributiveCategory)

module Categories.Gel.Maybe {o m ℓ} (𝓒 : DistributiveCategory o m ℓ) where

open import Level using (Level)

open import Categories.Gel.Distributive 𝓒
open DistributiveCategory 𝓒
open import Categories.Gel.Bool 𝓒 using (Bool; if_then_else_)

private
  variable
    a b : Level
    A : Obj → Set a
    B : Obj → Set b

record Maybe (A : Obj → Set a) ⦃ _ : Yoneda A ⦄ (X : Obj) : Set m where
  field
    unwrap : ⟦ Rep A ∐ ⋆ ⟧ X

instance
  yonedaMaybe : ⦃ _ : Yoneda A ⦄ → Yoneda (Maybe A)
  yonedaMaybe = record { wrap = λ x → record { unwrap = x } ; unwrap = Maybe.unwrap }

  module _ {A : Obj → Set a} ⦃ _ : Yoneda A ⦄ where
    open Yoneda (yonedaMaybe {A = A}) public using () renaming (presheaf to presheafMaybe)

fromMaybe : ⦃ _ : Yoneda A ⦄ → A ⟶ Maybe A ⇨ A
fromMaybe ⦃ yA ⦄ z mx = case unwrap mx of [ inj₁ x ⇒ wrap x ∥ inj₂ y ⇒ ! z ]
  where open Yoneda yA using (presheaf) -- Ugh.

maybe
  : ∀ {a b} {A : Obj → Set a} {B : Obj → Set b}
      ⦃ _ : Yoneda A ⦄ ⦃ _ : Yoneda B ⦄
  → B ⟶ (A ⇉ B) ⇨ Maybe A ⇨ B
maybe ⦃ _ ⦄ ⦃ yB ⦄ z f mx = case unwrap mx of [ inj₁ x ⇒ f (wrap x) ∥ inj₂ _ ⇒ ! z ]
  where open Yoneda yB using (presheaf)

nothing : ∀ {a} {A : Obj → Set a} ⦃ _ : Yoneda A ⦄ {X} → Maybe A X
nothing = record { unwrap = inj₂ ε }

just : ∀ {a} {A : Obj → Set a} ⦃ _ : Yoneda A ⦄ → A ⟶ Maybe A
just x = record { unwrap = inj₁ (unwrap x) }

justWhen : ∀ {a} {A : Obj → Set a} ⦃ _ : Yoneda A ⦄ → Bool ⟶ A ⇨ Maybe A
justWhen b x = if b then just x else nothing
