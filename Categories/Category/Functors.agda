{-# OPTIONS --safe #-}

module Categories.Category.Functors where

open import Level using (_⊔_)

open import Categories.Category using (Category; _[_∘_]; _[_⇒_]; _[_≈_]; RawCategory)
open import Categories.Functor using (Functor; RawFunctor; toRawFunctor)
open Categories.Functor.FunctorOperators
open import Categories.Inverse using
  ( Inverse; f⁻¹; _[_≅_]; inverse; _¹; _⁻¹; left-inverse; right-inverse
  ; ∘-inverseʳ; ∘-inverseˡ
  ; module InRaw
  )
open import Categories.NaturalTransformation using (_⟹_; α; _∘N_; wrapNT; NaturalTransformation)

module _
    {o₁ m₁ ℓ₁ o₂ m₂ ℓ₂}
    (𝓒 : Category o₁ m₁ ℓ₁)
    (𝓓 : Category o₂ m₂ ℓ₂)
    where

  private module 𝓒 = Category 𝓒
  private module 𝓓 = Category 𝓓

  Fun : Category (o₁ ⊔ m₁ ⊔ ℓ₁ ⊔ o₂ ⊔ m₂ ⊔ ℓ₂) (o₁ ⊔ m₁ ⊔ m₂ ⊔ ℓ₂) (o₁ ⊔ ℓ₂)
  Fun = record
    { Obj = Functor 𝓒 𝓓
    ; _⇒_ = _⟹_
    ; _≈_ = λ {A} {B} f g → ∀ {A} → f .α {A} ≈ g .α
    ; id = λ {F} → wrapNT record
        { α = 𝓓.id
        ; naturality = λ {A} {B} {f} →
            begin
              id ∘ F ₁ f

            ≈⟨ ∘-idˡ ⟩
              F ₁ f

            ≈˘⟨ ∘-idʳ ⟩
              F ₁ f ∘ id
            ∎
        }
    ; _∘_ = _∘N_
    ; equiv = record
        { refl = ≈.refl
        ; sym = λ x → ≈.sym x  -- η-expanded because type inference
        ; trans = λ x y → ≈.trans x y
        }
    ; ∘-resp-≈ = λ f₁≈f₂ g₁≈g₂ → ∘-resp-≈ f₁≈f₂ g₁≈g₂
    ; ∘-idˡ = ∘-idˡ
    ; ∘-idʳ = ∘-idʳ
    ; ∘-assocˡ = ∘-assocˡ
    }
    where
      open Category 𝓓
      open ≈-Reasoning

  -- A natural transformation with an inverse for each of its components
  -- is a natural isomorphism.  That is, the reverse naturality is
  -- derivable from the forward naturality and the reverse components.
  natIso
    : ∀ {F G : Functor 𝓒 𝓓}
    → (F⟹G : Fun [ F ⇒ G ])
    → (∀ {A} → Inverse 𝓓 (F⟹G .α {A}))
    → Fun [ F ≅ G ]
  natIso {F = F} {G} F⟹G α⁻¹ = record
    { _¹ = F⟹G
    ; _⁻¹ = wrapNT record
        { α = α⁻¹ .f⁻¹
        ; naturality =  λ {A} {B} {f} →
            begin
              α⁻¹ .f⁻¹ ∘ G ₁ f

            ≈˘⟨ ∘-inverseʳ 𝓓 (α⁻¹ .Inverse.inverse .left-inverse) ⟩
              ((α⁻¹ .f⁻¹ ∘ G ₁ f) ∘ F⟹G .α) ∘ α⁻¹ .f⁻¹

            ≈⟨ ≈.trans (∘-resp-≈ˡ ∘-assocʳ) ∘-assocʳ ⟩
              α⁻¹ .f⁻¹ ∘ (G ₁ f ∘ F⟹G .α) ∘ α⁻¹ .f⁻¹

            ≈˘⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ (F⟹G ._⟹_.naturality)) ⟩
              α⁻¹ .f⁻¹ ∘ (F⟹G .α ∘ F ₁ f) ∘ α⁻¹ .f⁻¹

            ≈⟨ ∘-resp-≈ʳ ∘-assocʳ ⟩
              α⁻¹ .f⁻¹ ∘ F⟹G .α ∘ F ₁ f ∘ α⁻¹ .f⁻¹

            ≈⟨ ∘-inverseˡ 𝓓 (α⁻¹ .Inverse.inverse .right-inverse) ⟩
              F ₁ f ∘ α⁻¹ .f⁻¹
            ∎
        }
    ; inverse = record
        { left-inverse = α⁻¹ .Inverse.inverse .right-inverse
        ; right-inverse = α⁻¹ .Inverse.inverse .left-inverse
        }
    }
    where
      open Category 𝓓
      open ≈-Reasoning

module _
    {o₁ m₁ ℓ₁ o₂ m₂ ℓ₂}
    {𝓒 : Category o₁ m₁ ℓ₁}
    {𝓓 : Category o₂ m₂ ℓ₂}
    where
  open Category 𝓓

  conj
    : ∀ {F G : Functor 𝓒 𝓓} {A B}
    → Fun 𝓒 𝓓 [ F ≅ G ]
    → G ₀ A ⇒ G ₀ B
    → F ₀ A ⇒ F ₀ B
  conj F≅G f = (F≅G ⁻¹) .α ∘ f ∘ (F≅G ¹) .α

  -- An identity morphism conjugated by a natural isomorphism is still
  -- an identity morphism.
  conj-id
    : ∀ {F G : Functor 𝓒 𝓓} {A}
    → (F≅G : Fun 𝓒 𝓓 [ F ≅ G ])
    → conj F≅G id ≈ id {F ₀ A}
  conj-id F≅G = ≈.trans (∘-resp-≈ʳ ∘-idˡ) (F≅G .inverse .left-inverse)

  -- The actual work of conj-∘.
  elim-inverse
    : ∀ {A B C D E F} -- ...
        {f : E ⇒ F} {g : C ⇒ E} {h : D ⇒ C}
        {i : C ⇒ D} {j : B ⇒ C} {k : A ⇒ B}
    → h ∘ i ≈ id
    → (f ∘ g ∘ h) ∘ (i ∘ j ∘ k) ≈ f ∘ (g ∘ j) ∘ k
  elim-inverse {f = f} {g} {h} {i} {j} {k} h∘i≈id =
    begin
      (f ∘ g ∘ h) ∘ i ∘ j ∘ k

    ≈⟨ ≈.trans ∘-assocʳ (∘-resp-≈ʳ ∘-assocʳ) ⟩
      f ∘ g ∘ h ∘ i ∘ j ∘ k

    ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ʳ (∘-inverseˡ 𝓓 h∘i≈id)) ⟩
      f ∘ g ∘ j ∘ k

    ≈⟨ ∘-resp-≈ʳ ∘-assocˡ ⟩
      f ∘ (g ∘ j) ∘ k
    ∎
    where open ≈-Reasoning

  -- Composition under a natural isomorphism is still composition.
  conj-∘
    : ∀ {F G : Functor 𝓒 𝓓} {A B C}
        {f : G ₀ B ⇒ G ₀ C}
        {g : G ₀ A ⇒ G ₀ B}
    → (F≅G : Fun 𝓒 𝓓 [ F ≅ G ])
    → conj F≅G f ∘ conj F≅G g ≈ conj F≅G (f ∘ g)
  conj-∘ F≅G = elim-inverse (F≅G .inverse .right-inverse)

record NaturalIsomorphism
    {o₁ m₁ ℓ₁ o₂ m₂ ℓ₂}
    {𝓒 : RawCategory o₁ m₁ ℓ₁}
    {𝓓 : RawCategory o₂ m₂ ℓ₂}
    (F G : RawFunctor 𝓒 𝓓) : Set (o₁ ⊔ m₁ ⊔ m₂ ⊔ ℓ₂) where
  field
    _¹ : NaturalTransformation F G
    _⁻¹ : NaturalTransformation G F
    left-inverse
      : ∀ {A}
      → InRaw._Retracts_ 𝓓 (_⁻¹ .α {A}) (_¹ .α)
    right-inverse
      : ∀ {A}
      → InRaw._Retracts_ 𝓓 (_¹ .α {A}) (_⁻¹ .α)

open NaturalIsomorphism public

-- [Note: wrapNatIso]
--
-- Since categories and functors contain potentially large equivalence
-- proofs, type-checking a natural isomorphism can be extremely costly
-- if the functors actually match but are obtained by syntactically
-- different terms.  Yet, we don't actually need to care if the proofs
-- are equal, since the record fields of a natural isomorphism
-- ultimately don't involve them.
--
-- To fix this, we can break the link that requires the proofs to be
-- unified, by using `wrapNatIso` and `unwrapNatIso` to "cast" it.
-- This way, the categories and functors expected by the context are
-- instantly unified with a type variable, and the categories and
-- functors involved in the given `NaturalIsomorphism` only need to
-- unify the relevant record fields.
--
-- In practice, this can save enough time to save a module that was
-- otherwise hanging during type-checking.

-- Construct a natural isomorphism from a more minimal record that
-- doesn't have the entire categories and functors in its type.
wrapNatIso
  : ∀ {o₁ m₁ ℓ₁ o₂ m₂ ℓ₂}
      {𝓒 : Category o₁ m₁ ℓ₁} {𝓓 : Category o₂ m₂ ℓ₂}
      {F G : Functor 𝓒 𝓓}
  → NaturalIsomorphism (toRawFunctor F) (toRawFunctor G)
  → Fun _ _ [ F ≅ G ]
wrapNatIso F≅G = record
  { _¹ = wrapNT (F≅G ¹)
  ; _⁻¹ = wrapNT (F≅G ⁻¹)
  ; inverse = record
      { left-inverse = F≅G .left-inverse
      ; right-inverse = F≅G .right-inverse
      }
  }

unwrapNatIso
  : ∀ {o₁ m₁ ℓ₁ o₂ m₂ ℓ₂}
      {𝓒 : Category o₁ m₁ ℓ₁} {𝓓 : Category o₂ m₂ ℓ₂}
      {F G : Functor 𝓒 𝓓}
  → Fun _ _ [ F ≅ G ]
  → NaturalIsomorphism (toRawFunctor F) (toRawFunctor G)
unwrapNatIso F≅G = record
  { _¹ = (F≅G ¹) ._⟹_.nt
  ; _⁻¹ = (F≅G ⁻¹) ._⟹_.nt
  ; left-inverse = F≅G .inverse .left-inverse
  ; right-inverse = F≅G .inverse .right-inverse
  }
