open import Categories.CartesianClosed using (CartesianClosedCategory)

module Categories.Gel.CartesianClosed
    {o m ℓ} (𝓒 : CartesianClosedCategory o m ℓ) where

open CartesianClosedCategory 𝓒

open import Categories.Gel.Cartesian cartesianCategory public

lambda : ∀ {A B} → (⟦ A ⟧ ⇉ ⟦ B ⟧) ⟶ ⟦ A ↝ B ⟧
lambda f = curryˡ (_↣_.unwrap (reify f))

infixr -2 lambda
syntax lambda (λ x → e) = Λ x ↝ e

_⟨$⟩_ : ∀ {A B} → ⟦ A ↝ B ⟧ ⟶ ⟦ A ⟧ ⇨ ⟦ B ⟧
f ⟨$⟩ x = uncurryˡ f $ x △ id
