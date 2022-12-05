{-# OPTIONS --sized-types #-}

module Circuits.Sandbox where

open import Data.List using (List; []; _∷_)
open import Data.Nat using ()
open import Data.Product using (proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (tt)
open import Level using (zero)


open import Mealy

𝓒 = MealyMachines {zero}

open import Categories.Gel.Distributive 𝓒 hiding (proj₁; inj₁; inj₂)

open import Circuits.Counter {𝓒 = 𝓒} causal
open import Circuits.Binary 𝓒
open import Circuits.Bit 𝓒

example₁ : List _
example₁ = proj₁ (steps (unwrap (counter {4} zeros)) (tt ∷ tt ∷ tt ∷ tt ∷ []))

example₂ : List _
example₂ =
  proj₁
    (steps
      (reify′ (λ x → counterEn {4} zeros x))
      (inj₁ tt ∷ inj₂ tt ∷ inj₂ tt ∷ inj₁ tt ∷ []))
