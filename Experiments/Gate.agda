module Experiments.Gate where

-- An inductive family describing a set of primitive operations:
-- constant 1, constant 0, and nand of two operands.

open import Function using (_∘_)
open import Data.Bool using (Bool; if_then_else_)
open import Data.Nat
open import Data.Vec using (Vec; _∷_; []; [_])
open import Data.String

open import Data.Bit

data Gate (A : Set) : ℕ → Set where
  high : Gate A 1
  low : Gate A 1
  NAND : (x y : A) → Gate A 1

map : ∀ {A B : Set} {n} → (A → B) → Gate A n → Gate B n
map f high = high
map f low = low
map f (NAND x y) = NAND (f x) (f y)

evalGate : ∀ {k} → Gate Bit k → Vec Bit k
evalGate high = one ∷ []
evalGate low = zero ∷ []
evalGate (NAND x y) = x ↑ y ∷ []

evalGate′ : ∀ {k A} → (A → Bit) → Gate A k → Vec Bit k
evalGate′ v = evalGate ∘ map v

gateDepth : ∀ {n} → Gate ℕ n → Vec ℕ n
gateDepth high = [ 0 ]
gateDepth low = [ 0 ]
gateDepth (NAND x y) = [ suc (x ⊔ y) ]

-- Algebra(-ish) for computing the size of the unfolding of the
-- DAG to a tree.
gateTreeSize : ∀ {n} → Gate ℕ n → Vec ℕ n
gateTreeSize high = [ 0 ]
gateTreeSize low = [ 0 ]
gateTreeSize (NAND x y) = [ 1 + x + y ]

Fmt : Set
Fmt = ℕ → String

maybeParens : Bool → String → String
maybeParens b s = if b then "(" ++ s ++ ")" else s

formatGateTree : ∀ {n} → Gate Fmt n → Vec Fmt n
formatGateTree high = [ (λ _ → "high") ]
formatGateTree low = [ (λ _ → "low") ]
formatGateTree (NAND x y) = [ (λ p → maybeParens (0 <ᵇ p) (x 1 ++ " ↑ " ++ y 1)) ]
