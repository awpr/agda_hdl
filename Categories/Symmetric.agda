{-# OPTIONS --safe #-}

module Categories.Symmetric where

open import Level using (Level; _⊔_; suc)

open import Categories.Category using (Category)
open import Categories.Braided using (BraidedMonoidal; BraidedMonoidalCategory; bundle)
import Categories.Inverse

record Symmetric {o m ℓ} (𝓒 : BraidedMonoidalCategory o m ℓ) : Set (o ⊔ ℓ) where
  open BraidedMonoidalCategory 𝓒
  open Categories.Inverse.In 𝓤 using (_InverseOf_)

  field
    braid-involutive : ∀ {A B} → braid {A} {B} ∘ braid ≈ id

  braid-inverse : ∀ {A B} → braid {A} {B} InverseOf braid
  braid-inverse = record
    { left-inverse = braid-involutive
    ; right-inverse = braid-involutive
    }

record SymmetricMonoidal {o m ℓ} (𝓒 : Category o m ℓ) : Set (o ⊔ m ⊔ ℓ) where
  constructor bundle
  field
    {braided} : BraidedMonoidal 𝓒
    symmetric : Symmetric (bundle braided)

  open BraidedMonoidal braided public
  open Symmetric symmetric public

record SymmetricMonoidalCategory (o m ℓ : Level) : Set (suc (o ⊔ m ⊔ ℓ)) where
  constructor bundle
  field
    {𝓤} : Category o m ℓ
    symmetric : SymmetricMonoidal 𝓤

  open Category 𝓤 public
  open SymmetricMonoidal symmetric public
