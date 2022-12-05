open import Categories.Cartesian using (CartesianCategory)
open import Categories.CausalLoop using (Causal)

module Categories.Gel.CausalLoop
  {o m ℓ}
  (𝓒 : CartesianCategory o m ℓ)
  (Loop : Causal (CartesianCategory.monoidalCategory 𝓒))
  where

open CartesianCategory 𝓒 hiding (_×_)
open import Categories.Gel.Cartesian 𝓒
open import Categories.Gel.Product 𝓒

unfold
  : ∀ {a s} {A : Obj → Set a} {S : Obj → Set s}
      ⦃ _ : Yoneda A ⦄ ⦃ _ : Yoneda S ⦄
  → S ⋆
  → (S ⇉ S × A) ⟶ A
unfold s₀ f = wrap (Causal.loop Loop (unwrap s₀) (unwrap (_↣_.unwrap (reify f))))
