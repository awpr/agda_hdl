{-# OPTIONS --safe #-}

module Categories.ClosedMonoidal where

open import Data.Product using (_,_)
open import Level using (_⊔_)

open import Categories.Adjunction using (_⊣_)
open import Categories.Bifunctor using (Bifunctor; Partialˡ; Partialʳ)
open import Categories.Category using (Category)
open import Categories.Constructions.Opposite using (_ᵒᵖ)
open import Categories.Functor using (Functor)
open import Categories.Monoidal using (Monoidal)
open Categories.Functor.FunctorOperators using (_₀_; _₁_)

-- See https://ncatlab.org/nlab/show/residual
--
-- Backslash is forbidden as an operator name, so we have to come up
-- with a different naming scheme for left and right residuals.  Let's
-- go with arrows whose lines are in the same direction as the
-- respective slashes, and whose heads point from the "argument" to
-- the "result".  That is, `A \ B` becomes `A ↘ B` and `B / A` becomes
-- `B ↙ A`.  These arrows are \dr and \dl, respectively.

record LeftClosed
    {o m ℓ} {𝓒 : Category o m ℓ} (monoidal : Monoidal 𝓒)
    : Set (o ⊔ m ⊔ ℓ) where
  open Category 𝓒
  open Monoidal monoidal

  field
    -↘- : Bifunctor (𝓒 ᵒᵖ) 𝓒 𝓒

  open Bifunctor -↘- public
    using ()
    renaming
      ( bimap₀ to infixr 30 _↘_
      ; Partialˡ to infix 30 -↘_
      ; Partialʳ to infix 30 _↘-
      ; bimap₁ to dimap
      ; first to lmap
      ; second to rmap
      )

  field
    left-residual : ∀ {A} → A ⊗- ⊣ A ↘-

  module _ {A} where
    open _⊣_ (left-residual {A}) public
      using ()
      renaming
        ( left-adjunct to uncurryˡ
        ; right-adjunct to curryˡ
        ; counit to evalˡ
        -- ; unit to <curried tuple constructor>, perhaps?
        )

record RightClosed
    {o m ℓ} {𝓒 : Category o m ℓ} (monoidal : Monoidal 𝓒)
    : Set (o ⊔ m ⊔ ℓ) where
  open Category 𝓒
  open Monoidal monoidal

  field
    -↙- : Bifunctor 𝓒 (𝓒 ᵒᵖ) 𝓒

  open Bifunctor -↙- public
    using ()
    renaming
      ( bimap₀ to infixr 30 _↙_
      ; Partialˡ to infix 30 -↙_
      ; Partialʳ to infix 30 _↙-
      -- With the "backwards" order of _↙_, these names don't line up
      -- with their conventionally-expected types, so let's just not
      -- re-export them.  They can still be accessed via the functor.
      -- ; bimap₁ to dimap
      -- ; lmap₁ to lmap
      -- ; rmap₁ to rmap
      )

  field
    right-residual : ∀ {A} → -⊗ A ⊣ -↙ A

  module _ {A} where
    open _⊣_ (right-residual {A}) public
      using ()
      renaming
        ( left-adjunct to uncurryʳ
        ; right-adjunct to curryʳ
        ; counit to evalʳ
        -- ; unit to <curried tuple constructor>, perhaps?
        )

record Biclosed
    {o m ℓ} {𝓒 : Category o m ℓ} (monoidal : Monoidal 𝓒)
    : Set (o ⊔ m ⊔ ℓ) where
  field
    left-closed : LeftClosed monoidal
    right-closed : RightClosed monoidal

  open LeftClosed left-closed public
  open RightClosed right-closed public
