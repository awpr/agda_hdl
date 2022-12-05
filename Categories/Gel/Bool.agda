open import Categories.Distributive using (DistributiveCategory)

module Categories.Gel.Bool {o m ℓ} (𝓒 : DistributiveCategory o m ℓ) where

import Data.Bool

open import Categories.Gel.Distributive 𝓒

open DistributiveCategory 𝓒

-- Constructor order: i₁ → zero; i₂ → one
Bool′ : Obj
Bool′ = ⋆ ∐ ⋆

record Bool (X : Obj) : Set m where
  field
    unwrap : ⟦ Bool′ ⟧ X

instance
  yonedaBool : Yoneda Bool
  yonedaBool = record { wrap = λ x → record { unwrap = x } ; unwrap = Bool.unwrap }

  open Yoneda yonedaBool public using () renaming (presheaf to presheafBool)

false true : ∀ {X} → Bool X
false = wrap (inj₁ ε)
true = wrap (inj₂ ε)

-- Create a constant `Bool` element from an Agda `Bool`.
fromBool : ∀ {X} → Data.Bool.Bool → Bool X
fromBool Data.Bool.true = true
fromBool Data.Bool.false = false

if_then_else_ : ∀ {a} {A : Obj → Set a} ⦃ _ : Yoneda A ⦄ → Bool ⟶ A ⇨ A ⇨ A
if_then_else_ ⦃ yA ⦄ b t f = case unwrap b of [ inj₁ _ ⇒ ! f ∥ inj₂ _ ⇒ ! t ]
  where open Yoneda yA using (presheaf)

not : Bool ⟶ Bool
not x = if x then false else true

and _∧_ : Bool ⟶ Bool ⇨ Bool
_∧_ = and
and x y = if x then y else false

or _∨_ : Bool ⟶ Bool ⇨ Bool
_∨_ = or
or x y = if x then true else y

xor _≠_ : Bool ⟶ Bool ⇨ Bool
_≠_ = xor
xor x y = do
  y′ ← y
  if ! x then not y′ else y′
  where open DoNotation
