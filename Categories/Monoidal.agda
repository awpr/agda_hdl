{-# OPTIONS --safe #-}

module Categories.Monoidal where

open import Data.Product using (_,_)
open import Function using (_$_)
open import Level using (Level; _⊔_; suc)

open import Categories.Bifunctor using
  ( Bifunctor; Partialˡ; Partialʳ; Flip
  ; LeftAssociated; RightAssociated
  )
open import Categories.Category using (Category)
open import Categories.Constructions.Product using (_⨂_)
open import Categories.Functor using (Functor; Id; _○_; _▲_; P₁; P₂; Assocˡ)
open Categories.Functor.FunctorOperators using (_₀_; _₁_)
open import Categories.Category.Functors using (Fun)
open import Categories.Inverse using
  ( _[_≅_]; _¹; _⁻¹
  ; InverseOf-sym; inverse; right-inverse; left-inverse
  )
open import Categories.NaturalTransformation using (α; naturality; wrapNT)

module _ {o m ℓ} (𝓒 : Category o m ℓ) where
  record Monoidal : Set (o ⊔ m ⊔ ℓ) where
    open Category 𝓒
    open Categories.Inverse.In 𝓒 using (_InverseOf_)

    field
      𝟏 : Obj
      -⊗- : Bifunctor 𝓒 𝓒 𝓒

    infixr 40 _⊗_
    _⊗_ : Obj → Obj → Obj
    A ⊗ B = -⊗- ₀ (A , B)

    bimap⊗ : ∀ {A B C D} → (A ⇒ C) → (B ⇒ D) → A ⊗ B ⇒ C ⊗ D
    bimap⊗ f g = -⊗- ₁ (f , g)

    infix 40 _⊗- -⊗_
    _⊗- : Obj → Functor 𝓒 𝓒
    A ⊗- = Partialʳ -⊗- A

    -⊗_ : Obj → Functor 𝓒 𝓒
    -⊗ B = Partialˡ -⊗- B

    -⊗-⊗- : Functor (𝓒 ⨂ 𝓒 ⨂ 𝓒) 𝓒
    -⊗-⊗- = RightAssociated -⊗-

    [-⊗-]⊗- : Functor (𝓒 ⨂ 𝓒 ⨂ 𝓒) 𝓒
    [-⊗-]⊗- = LeftAssociated -⊗-

    field
      assoc : Fun (𝓒 ⨂ 𝓒 ⨂ 𝓒) 𝓒 [ RightAssociated -⊗- ≅ LeftAssociated -⊗- ]
      unitˡ : Fun 𝓒 𝓒 [ Id ≅ 𝟏 ⊗- ]
      unitʳ : Fun 𝓒 𝓒 [ Id ≅ -⊗ 𝟏 ]

    assocˡ : ∀ {A B C} → A ⊗ B ⊗ C ⇒ (A ⊗ B) ⊗ C
    assocˡ = (assoc ¹) .α

    assocʳ : ∀ {A B C} → (A ⊗ B) ⊗ C ⇒ A ⊗ B ⊗ C
    assocʳ = (assoc ⁻¹) .α

    unitˡ⁺ : ∀ {A} → A ⇒ 𝟏 ⊗ A
    unitˡ⁺ = (unitˡ ¹) .α

    unitˡ⁻ : ∀ {A} → 𝟏 ⊗ A ⇒ A
    unitˡ⁻ = (unitˡ ⁻¹) .α

    unitʳ⁺ : ∀ {A} → A ⇒ A ⊗ 𝟏
    unitʳ⁺ = (unitʳ ¹) .α

    unitʳ⁻ : ∀ {A} → A ⊗ 𝟏 ⇒ A
    unitʳ⁻ = (unitʳ ⁻¹) .α

    first⊗ : ∀ {A B C} → A ⇒ C → A ⊗ B ⇒ C ⊗ B
    first⊗ f = bimap⊗ f id

    second⊗ : ∀ {A B C} → B ⇒ C → A ⊗ B ⇒ A ⊗ C
    second⊗ f = bimap⊗ id f

record MonoidalCategory (o m ℓ : Level) : Set (suc (o ⊔ m ⊔ ℓ)) where
  constructor bundle
  field
    {𝓤} : Category o m ℓ
    monoidal : Monoidal 𝓤

  open Category 𝓤 public
  open Monoidal monoidal public

FlipMC : ∀ {o m ℓ} → MonoidalCategory o m ℓ → MonoidalCategory o m ℓ
FlipMC 𝓒 = bundle $
  record
    { 𝟏 = 𝓒.𝟏
    ; -⊗- = Flip 𝓒.-⊗-
    ; assoc = record
        { _¹ = wrapNT record
          { α = (𝓒.assoc ⁻¹) .α
          ; naturality = (𝓒.assoc ⁻¹) .naturality
          }
        ; _⁻¹ = wrapNT record
          { α = (𝓒.assoc ¹) .α
          ; naturality = (𝓒.assoc ¹) .naturality
          }
        ; inverse = record
          { left-inverse = 𝓒.assoc .inverse .right-inverse
          ; right-inverse = 𝓒.assoc .inverse .left-inverse
          }
        }
    ; unitˡ = 𝓒.unitʳ
    ; unitʳ = 𝓒.unitˡ
    }
  where module 𝓒 = MonoidalCategory 𝓒
