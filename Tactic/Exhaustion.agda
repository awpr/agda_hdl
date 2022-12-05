module Tactic.Exhaustion where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_; uncurry)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)
open import Function using (_$-)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Data.Finite

exhaustion
  : ∀ {a A} {{_ : IsFinite A}}
  → (P : A → Set a)
  → {{ps : All P enumerate}}
  → (x : A) → P x
exhaustion {{fin}} P {{ps}} = IsFinite.all fin P ps

exhaustion₂
  : ∀ {a A B}
  → {{_ : IsFinite A}}
  → {{_ : IsFinite B}}
  → (P : A → B → Set a)
  → {{ps : All (uncurry P) enumerate}}
  → (x : A) → (y : B) → P x y
exhaustion₂ P x y = exhaustion (uncurry P) (x , y)

exhaustion₃
  : ∀ {a A B C}
  → {{_ : IsFinite A}}
  → {{_ : IsFinite B}}
  → {{_ : IsFinite C}}
  → (P : A → B → C → Set a)
  → {{ps : All (uncurry (uncurry P)) enumerate}}
  → (x : A) → (y : B) → (z : C) → P x y z
exhaustion₃ P x y z = exhaustion (uncurry (uncurry P)) ((x , y) , z)

instance
  all-vacuous
    : ∀ {a b} {A : Set a} {P : A → Set b}
    → All P []
  all-vacuous = []

  all-cons
    : ∀ {a b} {n : ℕ} {A : Set a} {P : A → Set b} {x : A} {xs : Vec A n}
    → {{P x}} → {{All P xs}} → All P (x ∷ xs)
  all-cons {{px}} {{pxs}} = px ∷ pxs

module Examples where
  open import Instances
  open import Data.Bit

  example₁ : ∀ {x} → not (not x) ≡ x
  example₁ = exhaustion (λ x → not (not x) ≡ x) $-

  example₂ : ∀ {x y} → x ∨ y ≡ not (not x ∧ not y)
  example₂ {x} {y} = exhaustion₂ (λ x y → x ∨ y ≡ not (not x ∧ not y)) x y
