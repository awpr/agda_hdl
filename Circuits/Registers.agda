open import Categories.Distributive using (DistributiveCategory)
open import Categories.CausalLoop using (Causal)

module Circuits.Registers
  {o m ℓ}
  {𝓒 : DistributiveCategory o m ℓ}
  (Loop : Causal (DistributiveCategory.monoidalCategory 𝓒))
  where

open import Data.Nat using (ℕ; suc; zero)
open import Level using (Level)

open DistributiveCategory 𝓒

open import Categories.Gel.Distributive 𝓒
open import Categories.Gel.CausalLoop cartesianCategory Loop
open import Categories.Gel.Maybe 𝓒 using (Maybe; fromMaybe; presheafMaybe; justWhen)
open import Categories.Gel.Product cartesianCategory
open import Categories.Gel.Vec cartesianCategory

open import Circuits.Bit 𝓒 using (Bit)

private
  variable
    a b : Level
    A : Obj → Set a
    B : Obj → Set b

flop
  : ⦃ _ : Yoneda A ⦄
  → A ⋆ → A ⟶ A
flop ⦃ yA ⦄ x₀ x = unfold x₀ (λ s → s , (! x))
  where open Yoneda yA using (presheaf)

delay
  : ⦃ _ : Yoneda A ⦄
  → ℕ
  → A ⋆
  → A ⟶ A
delay zero x₀ x = x
delay (suc n) x₀ x = flop x₀ (delay n x₀ x)

latest
  : ⦃ _ : Yoneda A ⦄
  → A ⋆
  → Maybe A ⟶ A
latest ⦃ yA ⦄ x₀ mx =
    unfold x₀ (λ s → s , fromMaybe s (! mx))
  where open Yoneda yA using (presheaf)

flopEnable
  : ⦃ _ : Yoneda A ⦄
  → A ⋆
  → Bit ⟶ A ⇨ A
flopEnable x₀ en x = latest x₀ (justWhen en x)

-- Vec order: index zero is the input from one cycle ago.
belt
  : ∀ {n} ⦃ _ : Yoneda A ⦄
  → A ⋆
  → A ⟶ Vec A n
belt {n = zero} _ _ = []
belt {n = suc n} ⦃ yA ⦄ x₀ x = do
   x′ ← flop x₀ x
   xs′ ← belt x₀ x′
   x′ ∷ xs′
 where
   open DoNotation
   open Yoneda yA using (presheaf)
