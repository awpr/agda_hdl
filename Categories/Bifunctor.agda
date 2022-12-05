{-# OPTIONS --safe #-}

module Categories.Bifunctor where

open import Data.Product using (_,_)
open import Level using (_⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Categories.Category using (Category; _[_⇒_]; _[_∘_]; _[_≈_])
open import Categories.Category.Functors using (Fun)
open import Categories.Constructions.Product using (_⨂_)
open import Categories.Functor using
  ( Functor; map₁-id; map₁-∘; map₁-resp-≈
  ; _○_; P₁; P₂; _▲_
  )
open import Categories.NaturalTransformation using (_⟹_; α; naturality; wrapNT)

open Categories.Functor.FunctorOperators

Bifunctor
  : ∀ {o₁ m₁ ℓ₁ o₂ m₂ ℓ₂ o₃ m₃ ℓ₃}
  → Category o₁ m₁ ℓ₁
  → Category o₂ m₂ ℓ₂
  → Category o₃ m₃ ℓ₃
  → Set (o₁ ⊔ m₁ ⊔ ℓ₁ ⊔ o₂ ⊔ m₂ ⊔ ℓ₂ ⊔ o₃ ⊔ m₃ ⊔ ℓ₃)
Bifunctor 𝓒 𝓓 = Functor (𝓒 ⨂ 𝓓)

-- Annoyingly, I can't find any way to let a definition in a
-- parameterized module refer to other definitions in the same module
-- with different parameters; yet I want a parameterized submodule
-- `Bifunctor` that contains all of these bindings.  So: define most
-- of them in a private module, then re-export them below.
private
  module BifunctorImpl
      {o₁ m₁ ℓ₁ o₂ m₂ ℓ₂ o₃ m₃ ℓ₃}
      {𝓒 : Category o₁ m₁ ℓ₁}
      {𝓓 : Category o₂ m₂ ℓ₂}
      {𝓔 : Category o₃ m₃ ℓ₃}
      (F : Functor (𝓒 ⨂ 𝓓) 𝓔)
      where
    private module 𝓒 = Category 𝓒
    private module 𝓓 = Category 𝓓
    private module 𝓔 = Category 𝓔

    open Category.≈-Reasoning 𝓔

    Flip : Functor (𝓓 ⨂ 𝓒) 𝓔
    Flip = record
      { map₀ = λ (B , A) → F ₀ (A , B)
      ; map₁ = λ (g , f) → F ₁ (f , g)
      ; map₁-resp-≈ = λ (g₁≈g₂ , f₁≈f₂) → F ₂ (f₁≈f₂ , g₁≈g₂)
      ; map₁-id = F .map₁-id
      ; map₁-∘ = F .map₁-∘
      }

    Partialˡ : 𝓓.Obj → Functor 𝓒 𝓔
    Partialˡ B = record
      { map₀ = λ A → F ₀ (A , B)
      ; map₁ = λ f → F ₁ (f , 𝓓.id)
      ; map₁-resp-≈ = λ f≈g → F .map₁-resp-≈ (f≈g , 𝓓.≈.refl)
      ; map₁-id = F .map₁-id
      ; map₁-∘ = λ {_} {_} {_} {f} {g} →
          begin
            F ₁ (f 𝓒.∘ g , 𝓓.id)

          ≈⟨ F .map₁-resp-≈ (𝓒.≈.refl , 𝓓.≈.sym 𝓓.∘-idˡ) ⟩
            F ₁ (f 𝓒.∘ g , 𝓓.id 𝓓.∘ 𝓓.id)

          ≈⟨ F .map₁-∘ ⟩
            F ₁ (f , 𝓓.id) 𝓔.∘ F ₁ (g , 𝓓.id)
          ∎
      }

    bimap₀ : 𝓒.Obj → 𝓓.Obj → 𝓔.Obj
    bimap₀ A B = F ₀ (A , B)

    bimap₁ : ∀ {A₁ A₂ B₁ B₂} → A₁ 𝓒.⇒ B₁ → A₂ 𝓓.⇒ B₂ → bimap₀ A₁ A₂ 𝓔.⇒ bimap₀ B₁ B₂
    bimap₁ f g = F ₁ (f , g)

    first : ∀ {A₁ A₂ B₁} → A₁ 𝓒.⇒ B₁ → bimap₀ A₁ A₂ 𝓔.⇒ bimap₀ B₁ A₂
    first f = bimap₁ f 𝓓.id

    second : ∀ {A₁ A₂ B₂} → A₂ 𝓓.⇒ B₂ → bimap₀ A₁ A₂ 𝓔.⇒ bimap₀ A₁ B₂
    second = bimap₁ 𝓒.id

    first∘second
      : ∀ {A₁ A₂ B₁ B₂} {f : 𝓒 [ A₁ ⇒ B₁ ]} {g : 𝓓 [ A₂ ⇒ B₂ ] }
      → 𝓔 [ 𝓔 [ first f ∘ second g ] ≈ bimap₁ f g ]
    first∘second {f = f} {g} =
      begin
        𝓔 [ first f ∘ second g ]

      ≈˘⟨ F .map₁-∘ ⟩
        bimap₁ (𝓒 [ f ∘ 𝓒.id ]) (𝓓 [ 𝓓.id ∘ g ])

      ≈⟨ F .map₁-resp-≈ (𝓒.∘-idʳ , 𝓓.∘-idˡ) ⟩
        bimap₁ f g
      ∎

    second∘first
      : ∀ {A₁ A₂ B₁ B₂} {f : 𝓒 [ A₁ ⇒ B₁ ]} {g : 𝓓 [ A₂ ⇒ B₂ ] }
      → 𝓔 [ 𝓔 [ second g ∘ first f ] ≈ bimap₁ f g ]
    second∘first {f = f} {g} =
      begin
        𝓔 [ second g ∘ first f ]

      ≈˘⟨ F .map₁-∘ ⟩
        bimap₁ (𝓒 [ 𝓒.id ∘ f ]) (𝓓 [ g ∘ 𝓓.id ])

      ≈⟨ F .map₁-resp-≈ (𝓒.∘-idˡ , 𝓓.∘-idʳ) ⟩
        bimap₁ f g
      ∎

    first-second-comm
      : ∀ {A₁ A₂ B₁ B₂} {f : 𝓒 [ A₁ ⇒ B₁ ]} {g : 𝓓 [ A₂ ⇒ B₂ ]}
      → 𝓔 [ 𝓔 [ first f ∘ second g ] ≈ 𝓔 [ second g ∘ first f ] ]
    first-second-comm = 𝓔.≈.trans first∘second (𝓔.≈.sym second∘first)

module Bifunctor
    {o₁ m₁ ℓ₁ o₂ m₂ ℓ₂ o₃ m₃ ℓ₃}
    {𝓒 : Category o₁ m₁ ℓ₁}
    {𝓓 : Category o₂ m₂ ℓ₂}
    {𝓔 : Category o₃ m₃ ℓ₃}
    (F : Functor (𝓒 ⨂ 𝓓) 𝓔)
    where
  open BifunctorImpl F public

  Partialʳ : Category.Obj 𝓒 → Functor 𝓓 𝓔
  Partialʳ = BifunctorImpl.Partialˡ Flip

open Bifunctor public

Bifun
  : ∀ {o₁ m₁ ℓ₁ o₂ m₂ ℓ₂ o₃ m₃ ℓ₃}
  → Category o₁ m₁ ℓ₁
  → Category o₂ m₂ ℓ₂
  → Category o₃ m₃ ℓ₃
  → Category _ _ _
Bifun 𝓒 𝓓 𝓔 = Fun (𝓒 ⨂ 𝓓) 𝓔

module _
    {o₁ m₁ ℓ₁ o₂ m₂ ℓ₂ o₃ m₃ ℓ₃}
    {𝓒 : Category o₁ m₁ ℓ₁}
    {𝓓 : Category o₂ m₂ ℓ₂}
    {𝓔 : Category o₃ m₃ ℓ₃}
    where
  -- A natural transformation between two bifunctors can also be seen as
  -- a natural transformation between their flipped forms.
  flip⟹
    : {F G : Bifunctor 𝓒 𝓓 𝓔}
    → F ⟹ G → Flip F ⟹ Flip G
  flip⟹ F⟹G = wrapNT record { α = F⟹G .α ; naturality = F⟹G .naturality }

  partialʳ⟹
    : {F G : Bifunctor 𝓒 𝓓 𝓔}
    → F ⟹ G
    → (A : Category.Obj 𝓒)
    → Partialʳ F A ⟹ Partialʳ G A
  partialʳ⟹ F⟹G A = wrapNT record { α = F⟹G .α ; naturality = F⟹G .naturality }

  -- (More observation/documentation rather than real proof to be applied)
  Flip∘Flip
    : {F : Bifunctor 𝓒 𝓓 𝓔}
    → Flip (Flip F) ≡ F
  Flip∘Flip = refl

module _
    {o m ℓ}
    {𝓒 : Category o m ℓ}
    (F : Bifunctor 𝓒 𝓒 𝓒)
    where
  RightAssociated : Functor (𝓒 ⨂ 𝓒 ⨂ 𝓒) 𝓒
  RightAssociated = F ○ (P₁ ▲ F ○ P₂)

  LeftAssociated : Functor (𝓒 ⨂ 𝓒 ⨂ 𝓒) 𝓒
  LeftAssociated = F ○ (F ○ (P₁ ▲ P₁ ○ P₂) ▲ P₂ ○ P₂)
