{-# OPTIONS --safe #-}

module Categories.NaturalTransformation where

open import Level using (suc; _⊔_)

open import Categories.Category using (Category; _[_⇒_]; _[_∘_]; RawCategory)
open import Categories.Functor using (Functor; RawFunctor; toRawFunctor)
open Categories.Functor.FunctorOperators
open import Relation.Binary.PropositionalEquality.Extras as ≡ using (cast)

-- ⟹ isn't usable in agda-input by default; to add it in emacs:
-- * M-x customize-variable<RET>agda-input-user-translations<RET>
-- * Insert an entry with mapping `r==`
-- * To enter the translation, M-x insert-char<RET>27F9<RET>
-- * Apply and save.

record NaturalTransformation
    {o₁ m₁ ℓ₁} {𝓒 : RawCategory o₁ m₁ ℓ₁}
    {o₂ m₂ ℓ₂} {𝓓 : RawCategory o₂ m₂ ℓ₂}
    (F G : RawFunctor 𝓒 𝓓)
    : Set (o₁ ⊔ m₁ ⊔ m₂ ⊔ ℓ₂)
    where
  field
    α : ∀ {A} → RawCategory._⇒_ 𝓓 (F .RawFunctor.map₀ A) (G .RawFunctor.map₀ A)
    naturality
      : ∀ {A B} {f : RawCategory._⇒_ 𝓒 A B}
      → RawCategory._≈_ 𝓓
          (RawCategory._∘_ 𝓓 α (F .RawFunctor.map₁ f))
          (RawCategory._∘_ 𝓓 (G .RawFunctor.map₁ f) α)

open NaturalTransformation public

module _
    {o₁ m₁ ℓ₁ o₂ m₂ ℓ₂}
    {𝓒 : Category o₁ m₁ ℓ₁} -- \MCC
    {𝓓 : Category o₂ m₂ ℓ₂} -- \MCD
    where
  open Category 𝓓
  open ≈-Reasoning

  record _⟹_
      (F G : Functor 𝓒 𝓓)
      : Set (o₁ ⊔ m₁ ⊔ m₂ ⊔ ℓ₂)
      where
    constructor wrapNT
    field
      nt : NaturalTransformation (toRawFunctor F) (toRawFunctor G)

    open NaturalTransformation nt public

  open _⟹_ public

  _∘N_
    : ∀ {F G H : Functor 𝓒 𝓓}
    → G ⟹ H
    → F ⟹ G
    → F ⟹ H
  _∘N_ {F} {G} {H} G⟹H F⟹G = wrapNT record
    { α = G⟹H .α ∘ F⟹G .α
    ; naturality = λ {A} {B} {f} →
        begin
          (G⟹H .α ∘ F⟹G .α) ∘ F ₁ f

        ≈⟨ ∘-assocʳ ⟩
          G⟹H .α ∘ F⟹G .α ∘ F ₁ f

        ≈⟨ ∘-resp-≈ʳ (F⟹G .naturality) ⟩
          G⟹H .α ∘ G ₁ f ∘ F⟹G .α

        ≈⟨ ∘-assocˡ ⟩
          (G⟹H .α ∘ G ₁ f) ∘ F⟹G .α

        ≈⟨ ∘-resp-≈ˡ (G⟹H .naturality) ⟩
          (H ₁ f ∘ G⟹H .α) ∘ F⟹G .α

        ≈⟨ ∘-assocʳ ⟩
          H ₁ f ∘ G⟹H .α ∘ F⟹G .α
        ∎
    }
