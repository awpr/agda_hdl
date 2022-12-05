{-# OPTIONS --safe #-}

module Categories.Functor where

open import Data.Product using (_,_; proj₁; proj₂)
open import Function using (_∘_)
open import Level using (Level; _⊔_)

open import Categories.Category using (Category; _[_⇒_]; _[_∘_]; _[_≈_]; RawCategory; toRawCategory)
open import Categories.Constructions.Product using (_⨂_)

private
  variable
    o₁ m₁ ℓ₁ o₂ m₂ ℓ₂ o₃ m₃ ℓ₃ : Level

record Functor (𝓒 : Category o₁ m₁ ℓ₁) (𝓓 : Category o₂ m₂ ℓ₂)
    : Set (o₁ ⊔ o₂ ⊔ m₁ ⊔ m₂ ⊔ ℓ₁ ⊔ ℓ₂) where
  private
    module 𝓒 = Category 𝓒
    module 𝓓 = Category 𝓓

  field
    map₀ : 𝓒.Obj → 𝓓.Obj
    map₁ : ∀ {A B} → 𝓒 [ A ⇒ B ] → 𝓓 [ map₀ A ⇒ map₀ B ]
    map₁-resp-≈ : ∀ {A B} {f g : 𝓒 [ A ⇒ B ]} → 𝓒 [ f ≈ g ] → 𝓓 [ map₁ f ≈ map₁ g ]

    map₁-id : ∀ {A} → 𝓓 [ map₁ (𝓒.id {A}) ≈ 𝓓.id ]
    map₁-∘
      : ∀ {A B C} {f : 𝓒 [ B ⇒ C ]} {g : 𝓒 [ A ⇒ B ]}
      → 𝓓 [ map₁ (𝓒 [ f ∘ g ]) ≈ 𝓓 [ map₁ f ∘ map₁ g ] ]

open Functor public

module FunctorOperators where
  -- Application-like (high-precedence) operator forms of the functor
  -- actions: use like 'F ₀ A' and 'F ₁ f ∘ F ₁ g'.
  open Functor
    using ()
    renaming
      ( map₀ to infixr 80 _₀_
      ; map₁ to infixr 80 _₁_
      ; map₁-resp-≈ to infixr 80 _₂_ -- Action on 2-cells, roughly
      )
    public

  -- _$_-like operator forms of the functor actions: use like 'F ₁$ G ₁$ f'.
  open Functor
    using ()
    renaming
      ( map₀ to infixr -1 _₀$_
      ; map₁ to infixr -1 _₁$_
      ; map₁-resp-≈ to infixr -1 _₂$_
      )
    public

private
  variable
    𝓒 : Category o₁ m₁ ℓ₁
    𝓓 : Category o₂ m₂ ℓ₂
    𝓔 : Category o₃ m₃ ℓ₃

-- The following bindings are level-polymorphic versions of
-- combinators that would constitute a category of categories.
-- Since there's not currently a level-polymorphic category
-- abstraction, the full generality can only be provided as standalone
-- functions, and an implementation of `Cat` would only include
-- categories and functors with the same set of level parameters.

-- ○ is \ci
infixr 40 _○_
_○_ : Functor 𝓓 𝓔 → Functor 𝓒 𝓓 → Functor 𝓒 𝓔
_○_ {𝓔 = 𝓔} F G = record
  { map₀ = F ₀_ ∘ G ₀_
  ; map₁ = F ₁_ ∘ G ₁_
  ; map₁-resp-≈ = F .map₁-resp-≈ ∘ G .map₁-resp-≈
  ; map₁-id = 𝓔.≈.trans (F ₂ G .map₁-id) (F .map₁-id)
  ; map₁-∘ = 𝓔.≈.trans (F ₂ G .map₁-∘) (F .map₁-∘)
  }
 where
  open FunctorOperators
  module 𝓔 = Category 𝓔

Id : Functor 𝓒 𝓒
Id {𝓒 = 𝓒} = record
  { map₀ = Function.id
  ; map₁ = Function.id
  ; map₁-resp-≈ = Function.id
  ; map₁-id = Category.≈.refl 𝓒
  ; map₁-∘ = Category.≈.refl 𝓒
  }

P₁
  : ∀ {o₁ m₁ ℓ₁ o₂ m₂ ℓ₂}
      {𝓒 : Category o₁ m₁ ℓ₁}
      {𝓓 : Category o₂ m₂ ℓ₂}
  → Functor (𝓒 ⨂ 𝓓) 𝓒
P₁ {𝓒 = 𝓒} = record
  { map₀ = proj₁
  ; map₁ = proj₁
  ; map₁-resp-≈ = proj₁
  ; map₁-id = 𝓒.≈.refl
  ; map₁-∘ = 𝓒.≈.refl
  }
  where module 𝓒 = Category 𝓒

P₂
  : ∀ {o₁ m₁ ℓ₁ o₂ m₂ ℓ₂}
      {𝓒 : Category o₁ m₁ ℓ₁}
      {𝓓 : Category o₂ m₂ ℓ₂}
  → Functor (𝓒 ⨂ 𝓓) 𝓓
P₂ {𝓓 = 𝓓} = record
  { map₀ = proj₂
  ; map₁ = proj₂
  ; map₁-resp-≈ = proj₂
  ; map₁-id = 𝓓.≈.refl
  ; map₁-∘ = 𝓓.≈.refl
  }
  where module 𝓓 = Category 𝓓

-- ▲ is \Tb3
infixr 20 _▲_
_▲_ : Functor 𝓒 𝓓 → Functor 𝓒 𝓔 → Functor 𝓒 (𝓓 ⨂ 𝓔)
_▲_ F G = record
  { map₀ = λ A → F ₀ A , G ₀ A
  ; map₁ = λ f → F ₁ f , G ₁ f
  ; map₁-resp-≈ = λ f≈g → F ₂ f≈g , G ₂ f≈g
  ; map₁-id = Functor.map₁-id F , Functor.map₁-id G
  ; map₁-∘ = Functor.map₁-∘ F , Functor.map₁-∘ G
  }
  where open FunctorOperators

Assocˡ : Functor (𝓒 ⨂ 𝓓 ⨂ 𝓔) ((𝓒 ⨂ 𝓓) ⨂ 𝓔)
Assocˡ = (P₁ ▲ P₁ ○ P₂) ▲ P₂ ○ P₂

-- Named by analogy to Haskell's `(***)`, this is the `bimap` of the
-- bifunctor `_⨂_` from `Cat × Cat` to `Cat`, but generalized to be
-- level-polymorphic.
--
-- ⁂ is \asterisk3
_⁂_
  : ∀ {o₄ m₄ ℓ₄} {𝓕 : Category o₄ m₄ ℓ₄}
  → Functor 𝓒 𝓓 → Functor 𝓔 𝓕 → Functor (𝓒 ⨂ 𝓔) (𝓓 ⨂ 𝓕)
F ⁂ G = F ○ P₁ ▲ G ○ P₂

record RawFunctor
    {o₁ m₁ ℓ₁ o₂ m₂ ℓ₂}
    (𝓒 : RawCategory o₁ m₁ ℓ₁)
    (𝓓 : RawCategory o₂ m₂ ℓ₂)
    : Set (o₁ ⊔ o₂ ⊔ m₁ ⊔ m₂)
    where
  field
    map₀ : RawCategory.Obj 𝓒 → RawCategory.Obj 𝓓
    map₁ : ∀ {A B} → RawCategory._⇒_ 𝓒 A B → RawCategory._⇒_ 𝓓 (map₀ A) (map₀ B)

toRawFunctor
  : ∀ {o₁ m₁ ℓ₁ o₂ m₂ ℓ₂} {𝓒 : Category o₁ m₁ ℓ₁} {𝓓 : Category o₂ m₂ ℓ₂}
  → Functor 𝓒 𝓓
  → RawFunctor (toRawCategory 𝓒) (toRawCategory 𝓓)
toRawFunctor F = record
  { map₀ = Functor.map₀ F
  ; map₁ = Functor.map₁ F
  }
