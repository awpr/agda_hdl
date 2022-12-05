{-#  OPTIONS --safe #-}

open import Categories.Category using (Category; _[_⇒_]; _[_∘_]; _[_≈_]; RawCategory; toRawCategory)

module Categories.Inverse where

open import Level using (_⊔_)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import Categories.Functor using (Functor)
open Categories.Functor.FunctorOperators

module InRaw {o m ℓ} (𝓒 : RawCategory o m ℓ) where
  open RawCategory 𝓒

  _Retracts_ : ∀ {A B} (f : A ⇒ B) (g : B ⇒ A) → Set ℓ
  f Retracts g = (f ∘ g) ≈ id

-- To bring inverses of a particular category into scope,
-- `open Categories.Inverse.In 𝓒`.
--
-- To use them parameterized, just `open import Categories.Inverse
-- using (<stuff>)`.  The present module re-exports the contents of
-- `Inverse`, renaming operators as needed to work with an explicit
-- Category parameter.
module In {o m ℓ} (𝓒 : Category o m ℓ) where
  open Category 𝓒

  open InRaw (toRawCategory 𝓒) using (_Retracts_) public

  -- A bidirectional morphism between `A` and `B`.
  --
  -- Currently sometimes used in place of _≅_ when it would be too
  -- much proof obligation all at once; such uses should be fixed when
  -- possible.
  record _⇔_ (A B : Obj) : Set (m ⊔ ℓ) where
    field
      to : A ⇒ B
      fro : B ⇒ A

  Retracts-∘
    : ∀ {A B C}
        {f₁ : B ⇒ C} {f₂ : A ⇒ B}
        {g₁ : C ⇒ B} {g₂ : B ⇒ A}
    → f₁ Retracts g₁
    → f₂ Retracts g₂
    → (f₁ ∘ f₂) Retracts (g₂ ∘ g₁)
  Retracts-∘ {f₁ = f₁} {f₂} {g₁} {g₂} f₁∘g₁≈id f₂∘g₂≈id =
    begin
      (f₁ ∘ f₂) ∘ (g₂ ∘ g₁)

    ≈⟨ ∘-assocˡ ⟩
      ((f₁ ∘ f₂) ∘ g₂) ∘ g₁

    ≈⟨ ∘-resp-≈ˡ ∘-assocʳ ⟩
      (f₁ ∘ (f₂ ∘ g₂)) ∘ g₁

    ≈⟨ ∘-resp-≈ˡ (∘-resp-≈ʳ f₂∘g₂≈id) ⟩
      (f₁ ∘ id) ∘ g₁

    ≈⟨ ∘-resp-≈ˡ ∘-idʳ ⟩
      f₁ ∘ g₁

    ≈⟨ f₁∘g₁≈id ⟩
      id
    ∎
    where open ≈-Reasoning

  --  Proof that `f` and `g` are (right- and left-) inverse.
  record _InverseOf_ {A B} (f : A ⇒ B) (g : B ⇒ A) : Set ℓ where
    field
      left-inverse : f Retracts g
      right-inverse : g Retracts f

  open _InverseOf_ public

  InverseOf-sym : ∀ {A B} {f : A ⇒ B} {g : B ⇒ A} → f InverseOf g → g InverseOf f
  InverseOf-sym x = record
    { left-inverse = x .right-inverse
    ; right-inverse = x .left-inverse
    }

  InverseOf-∘
    : ∀ {A B C} {f₁ : B ⇒ C} {g₁ : C ⇒ B} {f₂ : A ⇒ B} {g₂ : B ⇒ A}
    → f₁ InverseOf g₁
    → f₂ InverseOf g₂
    → (f₁ ∘ f₂) InverseOf (g₂ ∘ g₁)
  InverseOf-∘ {f₁ = f₁} {g₁} {f₂} {g₂} f₁g₁ f₂g₂ = record
    { left-inverse = Retracts-∘ (f₁g₁ .left-inverse) (f₂g₂ .left-inverse)
    ; right-inverse = Retracts-∘ (f₂g₂ .right-inverse) (f₁g₁ .right-inverse)
    }

  ∘-inverseʳ
    : ∀ {A B C}
        {f : B ⇒ A} {g : A ⇒ B} {h : A ⇒ C}
    → f ∘ g ≈ id → (h ∘ f) ∘ g ≈ h
  ∘-inverseʳ fg≈id = ≈.trans ∘-assocʳ (≈.trans (∘-resp-≈ʳ fg≈id) ∘-idʳ)

  ∘-inverseˡ
    : ∀ {A B C}
        {f : B ⇒ A} {g : A ⇒ B} {h : C ⇒ A}
    → f ∘ g ≈ id → f ∘ g ∘ h ≈ h
  ∘-inverseˡ fg≈id = ≈.trans ∘-assocˡ (≈.trans (∘-resp-≈ˡ fg≈id) ∘-idˡ)

  -- Rearrangement of equivalences by transposing inverses to the
  -- opposite side of the equality.

  open ≈-Reasoning

  transposeʳ⁺
    : ∀ {A B C}
        {f : A ⇒ B} {g : B ⇒ A}
        {h : B ⇒ C} {k : A ⇒ C}
    → f ∘ g ≈ id
    → h ∘ f ≈ k
    → h ≈ k ∘ g
  transposeʳ⁺ {f = f} {g} {h} {k} f∘g≈id h∘f≈k =
    begin
      h
    ≈˘⟨ ∘-inverseʳ f∘g≈id ⟩
      (h ∘ f) ∘ g
    ≈⟨ ∘-resp-≈ˡ h∘f≈k ⟩
      k ∘ g
    ∎

  transposeʳ⁻
    : ∀ {A B C}
        {f : A ⇒ B} {g : B ⇒ A}
        {h : B ⇒ C} {k : A ⇒ C}
    → g ∘ f ≈ id
    → h ≈ k ∘ g
    → h ∘ f ≈ k
  transposeʳ⁻ g∘f≈id h≈k∘g = ≈.sym (transposeʳ⁺ g∘f≈id (≈.sym h≈k∘g))

  transposeˡ⁺
    : ∀ {A B C}
        {f : A ⇒ B} {g : B ⇒ A}
        {h : C ⇒ B} {k : C ⇒ A}
    → f ∘ g ≈ id
    → g ∘ h ≈ k
    → h ≈ f ∘ k
  transposeˡ⁺ {f = f} {g} {h} {k} f∘g≈id g∘h≈k =
    begin
      h
    ≈˘⟨ ∘-inverseˡ f∘g≈id ⟩
      f ∘ (g ∘ h)
    ≈⟨ ∘-resp-≈ʳ g∘h≈k ⟩
      f ∘ k
    ∎

  transposeˡ⁻
    : ∀ {A B C}
        {f : A ⇒ B} {g : B ⇒ A}
        {h : C ⇒ B} {k : C ⇒ A}
    → g ∘ f ≈ id
    → h ≈ f ∘ k
    → g ∘ h ≈ k
  transposeˡ⁻ g∘f≈id h≈f∘k = ≈.sym (transposeˡ⁺ g∘f≈id (≈.sym h≈f∘k))

  -- An inverse morphism of `f`.
  --
  -- Except not actually (yet), for the sake of being able to
  -- implement and commit things incrementally.
  record RawInverse {A B} (f : A ⇒ B) : Set (m ⊔ ℓ) where
    field
      f⁻¹ : B ⇒ A
      -- inverse : f InverseOf f⁻¹

  -- An inverse morphism of `f`.
  record Inverse {A B} (f : A ⇒ B) : Set (m ⊔ ℓ) where
    field
      f⁻¹ : B ⇒ A
      inverse : f InverseOf f⁻¹

  -- Isomorphism between `A` and `B`.
  record _≅_ (A B : Obj) : Set (m ⊔ ℓ) where
    field
      _¹ : A ⇒ B
      _⁻¹ : B ⇒ A
      inverse : _⁻¹ InverseOf _¹

    isoToInverse : Inverse _¹
    isoToInverse = record { f⁻¹ = _⁻¹ ; inverse = InverseOf-sym inverse }

  open _≅_ public using (_¹; _⁻¹; inverse; isoToInverse)

  -- Scope games: if this `inverse` is in scope when defining _≅_, it
  -- doesn't seem to be possible to refer to its own record field
  -- `inverse` unambiguously inside the record-module.  So defer this
  -- `open` directive until after `_≅_` is defined.
  open Inverse public using (f⁻¹; inverse)

  ≅-refl : ∀ {A} → A ≅ A
  ≅-refl = record
    { _¹ = id
    ; _⁻¹ = id
    ; inverse = record
        { left-inverse = ∘-idˡ
        ; right-inverse = ∘-idˡ
        }
    }

  ≅-sym : ∀ {A B} → A ≅ B → B ≅ A
  ≅-sym A≅B = record
    { _¹ = A≅B ⁻¹
    ; _⁻¹ = A≅B ¹
    ; inverse = InverseOf-sym (_≅_.inverse A≅B)
    }

  ≅-trans : ∀ {A B C} → A ≅ B → B ≅ C → A ≅ C
  ≅-trans A≅B B≅C = record
    { _¹ = (B≅C ¹) ∘ (A≅B ¹)
    ; _⁻¹ = (A≅B ⁻¹) ∘ (B≅C ⁻¹)
    ; inverse = InverseOf-∘ (A≅B .inverse) (B≅C .inverse)
    }

  ≅-equiv : IsEquivalence _≅_
  ≅-equiv = record
    { refl = ≅-refl
    ; sym = ≅-sym
    ; trans = ≅-trans
    }

  Objects : Setoid o (m ⊔ ℓ)
  Objects = record
    { Carrier = Obj
    ; _≈_ = _≅_
    ; isEquivalence = ≅-equiv
    }

  module ≅-Reasoning = SetoidReasoning Objects

-- Explicit-parameter re-exports.
open In public
  using (RawInverse; Inverse; Objects; ∘-inverseˡ; ∘-inverseʳ)
  renaming
    ( _≅_ to _[_≅_]
    ; _InverseOf_ to _[_InverseOf_]
    ; _Retracts_ to _[_Retracts_]
    ; _⇔_ to _[_⇔_]
    )

-- Implicit-parameter re-exports.
module InverseImplicits {o m ℓ} {𝓒 : Category o m ℓ} = In 𝓒
open InverseImplicits
  public
  using
    ( ≅-refl; ≅-sym; ≅-trans; ≅-equiv
    ; _¹; _⁻¹; f⁻¹; inverse; left-inverse; right-inverse; isoToInverse
    ; InverseOf-∘; InverseOf-sym
    )

liftRetracts
  : ∀ {o₁ m₁ ℓ₁ o₂ m₂ ℓ₂} {𝓒 : Category o₁ m₁ ℓ₁} {𝓓 : Category o₂ m₂ ℓ₂}
      {A B} {f : 𝓒 [ A ⇒ B ]} {g : 𝓒 [ B ⇒ A ]}
  → (F : Functor 𝓒 𝓓)
  → 𝓒 [ 𝓒 [ f ∘ g ] ≈ Category.id 𝓒 ] → 𝓓 [ 𝓓 [ F ₁ f ∘ F ₁ g ] ≈ Category.id 𝓓 ]
liftRetracts {𝓒 = 𝓒} {𝓓} {f = f} {g} F f∘g≈id =
  begin
    F ₁ f ∘ F ₁ g

  ≈˘⟨ F .Functor.map₁-∘ ⟩
    F ₁ (𝓒 [ f ∘ g ])

  ≈⟨ F ₂ f∘g≈id ⟩
    F ₁ 𝓒.id

  ≈⟨ F .Functor.map₁-id ⟩
    id
  ∎
  where
    module 𝓒 = Category 𝓒
    open Category 𝓓
    open ≈-Reasoning

liftInverseOf
  : ∀ {o₁ m₁ ℓ₁ o₂ m₂ ℓ₂} {𝓒 : Category o₁ m₁ ℓ₁} {𝓓 : Category o₂ m₂ ℓ₂}
      {A B} {f : 𝓒 [ A ⇒ B ]} {g : 𝓒 [ B ⇒ A ]}
  → (F : Functor 𝓒 𝓓)
  → 𝓒 [ f InverseOf g ] → 𝓓 [ (F ₁ f) InverseOf (F ₁ g) ]
liftInverseOf {𝓓 = 𝓓} F fInvg = record
  { left-inverse = liftRetracts F (fInvg .left-inverse)
  ; right-inverse = liftRetracts F (fInvg .right-inverse)
  }
  where
    open Category 𝓓
    open ≈-Reasoning
