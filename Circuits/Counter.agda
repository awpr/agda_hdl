open import Categories.Distributive using (DistributiveCategory)
open import Categories.CausalLoop using (Causal)

module Circuits.Counter
  {o m ℓ}
  {𝓒 : DistributiveCategory o m ℓ}
  (Loop : Causal (DistributiveCategory.monoidalCategory 𝓒))
  where

open import Function using (_$_)

open DistributiveCategory 𝓒

open import Categories.Gel.Distributive 𝓒 hiding (_$_)
open import Categories.Gel.CausalLoop cartesianCategory Loop
open import Categories.Gel.Maybe 𝓒
open import Categories.Gel.Product cartesianCategory

open import Circuits.Binary 𝓒
open import Circuits.Bit 𝓒

counterRstEn
  : ∀ {n}
  → UInt n ⋆
  → Maybe (UInt n) ⟶ Bit ⇨ UInt n
counterRstEn x₀ rst en =
  unfold x₀ $ λ s →
    fromMaybe (snd (carry (! en) s)) (! rst) , s

counterRst
  : ∀ {n}
  → UInt n ⋆
  → Maybe (UInt n) ⟶ UInt n
counterRst x₀ rst = counterRstEn x₀ rst true

counterEn
  : ∀ {n}
  → UInt n ⋆
  → Bit ⟶ UInt n
counterEn x₀ en = counterRstEn x₀ nothing en

counter
  : ∀ {n X}
  → UInt n ⋆
  → UInt n X
counter x₀ = counterEn x₀ true
