{-# OPTIONS --safe #-}

module Categories.CartesianClosed where

open import Level using (Level; _⊔_; suc)

open import Categories.Adjunction using (_⊣_)
open import Categories.Bifunctor using (Bifunctor; Flip; module Bifunctor)
open import Categories.Category using (Category)
open import Categories.Cartesian using (Cartesian; CartesianCategory; bundle)
open import Categories.Constructions.Opposite using (_ᵒᵖ)
open import Categories.Monoidal using (Monoidal)
open import Categories.NaturalTransformation using (α)
open import Categories.ClosedMonoidal using (Biclosed)

record CartesianClosed {o m ℓ} (𝓒 : Category o m ℓ) : Set (o ⊔ m ⊔ ℓ) where
  open Category 𝓒

  field
    cartesian : Cartesian 𝓒
    -↝- : Bifunctor (𝓒 ᵒᵖ) 𝓒 𝓒

  open Cartesian cartesian public
  open Bifunctor -↝- public
    using ()
    renaming
      ( bimap₀ to infixr 30 _↝_
      ; Partialˡ to infix 30 -↝_
      ; Partialʳ to infix 30 _↝-
      )

  field
    -- Provide left and right currying independently, since although
    -- each is derivable from the other in this context, it can be
    -- more efficient to implement them directly than to implement one
    -- and adapt the other.
    left-residual : ∀ {A} → A ×- ⊣ A ↝-
    right-residual : ∀ {A} → -× A ⊣ A ↝-

  biclosed : Biclosed monoidal
  biclosed = record
    { left-closed = record { -↘- = -↝- ; left-residual = left-residual }
    ; right-closed = record { -↙- = Flip -↝- ; right-residual = right-residual }
    }

  open Biclosed biclosed public

  field
    -- The two adjunctions above are mutually derivable via the
    -- universal pairing morphisms; they must agree with each other
    -- under this derivation.
    curry-coherent : ∀ {A B C} (f : A × B ⇒ C) → curryʳ f ≈ curryˡ (f ∘ swap .α)
    uncurry-coherent : ∀ {A B C} (f : A ⇒ B ↝ C) → uncurryʳ f ≈ uncurryˡ f ∘ swap .α

  -- Not public: could want to open a different monoidal structure.
  open Monoidal monoidal

  app : ∀ {A B C} → (C ⇒ A ↝ B) → (C ⇒ A) → C ⇒ B
  app f x = uncurryˡ f ∘ first⊗ x ∘ δ

  flip : ∀ {A B C} → A ⇒ B ↝ C → B ⇒ A ↝ C
  flip f = curryʳ (uncurryˡ f)

record CartesianClosedCategory (o m ℓ : Level) : Set (suc (o ⊔ m ⊔ ℓ)) where
  constructor bundle
  field
    {𝓤} : Category o m ℓ
    cartesianClosed : CartesianClosed 𝓤

  open Category 𝓤 public
  open CartesianClosed cartesianClosed public

  cartesianCategory : CartesianCategory o m ℓ
  cartesianCategory = bundle cartesian

  open CartesianCategory cartesianCategory
    using (monoidalCategory; braidedMonoidalCategory)
    public
