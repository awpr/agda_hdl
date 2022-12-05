open import Categories.Cartesian using (CartesianCategory)

module Categories.Gel.Vec {o m ℓ} (C : CartesianCategory o m ℓ) where

open import Data.Nat using (ℕ; suc; zero)
import Data.Vec
open import Function using (it)
open import Level using (Level)

open CartesianCategory C hiding (_⇒_)

open import Categories.Gel.Cartesian C

Vec′ : Obj → ℕ → Obj
Vec′ A zero = ⋆
Vec′ A (suc n) = A × Vec′ A n

private
  variable
    a b : Level
    n : ℕ
    A B : Obj → Set a

record Vec (A : Obj → Set a) ⦃ _ : Yoneda A ⦄ (n : ℕ) (X : Obj) : Set m where
  constructor vec
  field
    unwrap : ⟦ Vec′ (Rep A) n ⟧ X

instance
  vecYoneda : ⦃ _ : Yoneda A ⦄ → Yoneda (Vec A n)
  vecYoneda = record { wrap = vec ; unwrap = Vec.unwrap }

  vecPresheaf : ⦃ _ : Yoneda A ⦄ → Presheaf (Vec A n)
  vecPresheaf = Yoneda.presheaf vecYoneda

infixr 5 _∷_
_∷_ : ⦃ _ : Yoneda A ⦄ → A ⟶ Vec A n ⇨ Vec A (suc n)
x ∷ vec xs = vec (unwrap x △ xs)

[] : ∀ {X} ⦃ _ : Yoneda A ⦄ → Vec A zero X
[] = vec ε

-- Build a vector of constant elements from an Agda vector.
fromVec
  : ∀ {a} {A′ : Set a} {n X} ⦃ _ : Yoneda A ⦄
  → (A′ → A X) → Data.Vec.Vec A′ n → Vec A n X
fromVec _ Data.Vec.[] = []
fromVec f (x Data.Vec.∷ xs) = f x ∷ fromVec f xs

head : ⦃ _ : Yoneda A ⦄ → Vec A (suc n) ⟶ A
head x = wrap (proj₁ (Vec.unwrap x))

tail : ⦃ _ : Yoneda A ⦄ → Vec A (suc n) ⟶ Vec A n
tail x = vec (proj₂ (Vec.unwrap x))

replicate : ∀ n ⦃ _ : Yoneda A ⦄ → A ⟶ Vec A n
replicate zero x = [] -- Just for tidiness.
replicate {A = A} n x0 = do
  x0′ ← x0
  go x0′
  where
    open DoNotation

    go : ∀ {n} → A ⟶ Vec A n
    go {zero} x = []
    go {suc n} x = x ∷ go x

-- `replicate`, but with the length inferred.
pure : ⦃ _ : Yoneda A ⦄ → A ⟶ Vec A n
pure {n = n} = replicate n

map : ⦃ _ : Yoneda A ⦄ ⦃ _ : Yoneda B ⦄ → (A ↣ B) ⟶ Vec A n ⇨ Vec B n
map {n = zero}  _ _  = []
map {n = suc n} ⦃ _ ⦄ ⦃ yB ⦄ f xs0 = do
  xs0′ ← xs0
  ((! f) $′ head xs0′) ∷ map (! f) (tail xs0′)
  where
    open DoNotation
    open Yoneda yB using (presheaf)
