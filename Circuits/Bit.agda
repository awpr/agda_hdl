open import Categories.Distributive using (DistributiveCategory)

module Circuits.Bit {o m ℓ} (𝓒 : DistributiveCategory o m ℓ) where

open DistributiveCategory 𝓒 hiding (_×_)

open import Categories.Gel.Bool 𝓒 public
open import Categories.Gel.Distributive 𝓒
open import Categories.Gel.Product cartesianCategory

open DoNotation

Bit : Obj → Set m
Bit = Bool

zero one : ∀ {X} → Bit X
zero = false
one = true

halfAdder : Bit ⟶ Bit ⇨ Bit × Bit
halfAdder x y = do
  x′ ← x
  y′ ← ! y
  and x′ y′ , xor x′ y′

fullAdder : Bit ⟶ Bit ⇨ Bit ⇨ Bit × Bit
fullAdder x y c = do
  xy ← halfAdder x y
  xyc ← halfAdder (snd xy) (! c)
  or (fst xy) (fst xyc) , snd xyc
