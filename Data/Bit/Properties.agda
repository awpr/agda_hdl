module Data.Bit.Properties where

open import Data.Bool.Properties public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)

open import Data.Bit

⊕-comm : ∀ x y → x ⊕ y ≡ y ⊕ x
⊕-comm zero zero = refl
⊕-comm zero one = refl
⊕-comm one zero = refl
⊕-comm one one = refl

⊕-assoc : ∀ x y z → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
⊕-assoc zero y z = refl
⊕-assoc one zero z = refl
⊕-assoc one one zero = refl
⊕-assoc one one one = refl

infixl 20 _∘_
_∘_ : ∀ {A : Set} {x y z : A} → y ≡ z → x ≡ y → x ≡ z
y≡z ∘ x≡y = trans x≡y y≡z

↑-comm : ∀ x y → x ↑ y ≡ y ↑ x
↑-comm x y = sym (↑-correct y x) ∘ cong not (∧-comm x y) ∘ ↑-correct x y
