{-# OPTIONS --safe #-}

module Categories.Cartesian where

open import Data.Product using (_,_)
open import Function using (_$_; flip)
open import Level using (Level; _⊔_; suc)

open import Categories.Bifunctor using
  ( Bifunctor; Partialˡ; Partialʳ; Flip; Bifun; RightAssociated; LeftAssociated
  ; flip⟹; partialʳ⟹
  )
open import Categories.Braided using (Braided; BraidedMonoidal; BraidedMonoidalCategory; bundle)
open import Categories.Category using (Category; _[_∘_]; _[_⇒_])
open import Categories.Category.Functors using (Fun; natIso; wrapNatIso; unwrapNatIso)
open import Categories.Constructions.Core using (Core)
open import Categories.Constructions.Product using (_⨂_)
open import Categories.Functor using (Functor; _○_; Id; P₁; P₂; _▲_)
open Categories.Functor.FunctorOperators
open import Categories.Inverse using (_[_InverseOf_]; _[_≅_]; _¹; _⁻¹; inverse; left-inverse; right-inverse)
open import Categories.Monoidal using (Monoidal; MonoidalCategory; bundle)
open import Categories.NaturalTransformation using (_⟹_; α; naturality; wrapNT)
open import Categories.Symmetric using (Symmetric)
open import Categories.Terminal using (TerminalObject)

module _ {o m ℓ} (𝓒 : Category o m ℓ) where
  record Cartesian : Set (o ⊔ m ⊔ ℓ) where
    open Category 𝓒
    open Categories.Inverse.In 𝓒 using (Inverse; _Retracts_)
    open ≈-Reasoning

    infixr 40 _×_
    infixr 20 _△_
    field
      terminal : TerminalObject 𝓒
      _×_ : Obj → Obj → Obj

      _△_ : ∀ {A B C} → A ⇒ B → A ⇒ C → A ⇒ B × C

      p₁ : ∀ {A B} → A × B ⇒ A
      p₂ : ∀ {A B} → A × B ⇒ B

      △-factors-p₁ : ∀ {A B C} {f : A ⇒ B} {g : A ⇒ C} → p₁ ∘ (f △ g) ≈ f
      △-factors-p₂ : ∀ {A B C} {f : A ⇒ B} {g : A ⇒ C} → p₂ ∘ (f △ g) ≈ g
      △-unique
        : ∀ {A B C} {f : A ⇒ B} {g : A ⇒ C} {f△g : A ⇒ B × C}
        → p₁ ∘ f△g ≈ f → p₂ ∘ f△g ≈ g → f△g ≈ f △ g

    △-unique′
        : ∀ {A B C} {f : A ⇒ B × C} {g : A ⇒ B × C}
        → p₁ ∘ f ≈ p₁ ∘ g
        → p₂ ∘ f ≈ p₂ ∘ g
        → f ≈ g
    △-unique′ {f = f} {g = g} f₁≈g₁ f₂≈g₂ =
      begin
        f

      ≈⟨ △-unique f₁≈g₁ f₂≈g₂ ⟩
        p₁ ∘ g △ p₂ ∘ g

      ≈˘⟨ △-unique ≈.refl ≈.refl ⟩
        g
      ∎

    △-resp-≈
      : ∀ {A B C} {f₁ f₂ : A ⇒ B} {g₁ g₂ : A ⇒ C}
      → f₁ ≈ f₂
      → g₁ ≈ g₂
      → f₁ △ g₁ ≈ f₂ △ g₂
    △-resp-≈ f₁≈f₂ g₁≈g₂ =
      △-unique (≈.trans △-factors-p₁ f₁≈f₂) (≈.trans △-factors-p₂ g₁≈g₂)

    △-resp-≈ˡ
      : ∀ {A B C} {f₁ f₂ : A ⇒ B} {g : A ⇒ C}
      → f₁ ≈ f₂
      → f₁ △ g ≈ f₂ △ g
    △-resp-≈ˡ f₁≈f₂ = △-resp-≈ f₁≈f₂ ≈.refl

    △-resp-≈ʳ
      : ∀ {A B C} {f : A ⇒ B} {g₁ g₂ : A ⇒ C}
      → g₁ ≈ g₂
      → f △ g₁ ≈ f △ g₂
    △-resp-≈ʳ g₁≈g₂ = △-resp-≈ ≈.refl g₁≈g₂

    △-dist
      : ∀ {A B C D}
          {f : B ⇒ C} {g : B ⇒ D} {h : A ⇒ B}
      → (f △ g) ∘ h ≈ f ∘ h △ g ∘ h
    △-dist = △-unique
      (≈.trans ∘-assocˡ (∘-resp-≈ˡ △-factors-p₁))
      (≈.trans ∘-assocˡ (∘-resp-≈ˡ △-factors-p₂))

    △-fuse
      : ∀ {A B₁ B₂ C₁ C₂}
          {f₁ : B₁ ⇒ B₂} {g₁ : C₁ ⇒ C₂}
          {f₂ : A ⇒ B₁} {g₂ : A ⇒ C₁}
      → (f₁ ∘ p₁ △ g₁ ∘ p₂) ∘ (f₂ △ g₂) ≈ f₁ ∘ f₂ △ g₁ ∘ g₂
    △-fuse {f₁ = f₁} {g₁} {f₂} {g₂} =
      begin
        (f₁ ∘ p₁ △ g₁ ∘ p₂) ∘ (f₂ △ g₂)

      ≈⟨ △-dist ⟩
        ((f₁ ∘ p₁) ∘ (f₂ △ g₂) △ (g₁ ∘ p₂) ∘ (f₂ △ g₂))

      ≈⟨ △-resp-≈ ∘-assocʳ ∘-assocʳ ⟩
        (f₁ ∘ p₁ ∘ (f₂ △ g₂) △ g₁ ∘ p₂ ∘ (f₂ △ g₂))

      ≈⟨ △-resp-≈ (∘-resp-≈ʳ △-factors-p₁) (∘-resp-≈ʳ △-factors-p₂) ⟩
        f₁ ∘ f₂ △ g₁ ∘ g₂
      ∎

    -- TODO: For some reason, I almost always want to use `sym` on
    -- `△-unique`; think about why and consider flipping its
    -- definition?
    △-η : ∀ {A B} → p₁ △ p₂ ≈ id {A × B}
    △-η = ≈.sym (△-unique ∘-idʳ ∘-idʳ)

    -×- : Bifunctor 𝓒 𝓒 𝓒
    -×- = record
      { map₀ = λ (A , B) → A × B
      ; map₁ = λ (f , g) → f ∘ p₁ △ g ∘ p₂
      ; map₁-resp-≈ = λ (f₁≈g₁ , f₂≈g₂) → △-resp-≈ (∘-resp-≈ˡ f₁≈g₁) (∘-resp-≈ˡ f₂≈g₂)
      ; map₁-id =
          ≈.sym
            (△-unique
              (≈.trans ∘-idʳ (≈.sym ∘-idˡ))
              (≈.trans ∘-idʳ (≈.sym ∘-idˡ)))
      ; map₁-∘ = λ
          { {_} {_} {_} {f = f₁ , f₂} {g = g₁ , g₂} →
            begin
              (f₁ ∘ g₁) ∘ p₁ △ (f₂ ∘ g₂) ∘ p₂

            ≈⟨ △-resp-≈ ∘-assocʳ ∘-assocʳ ⟩
              f₁ ∘ g₁ ∘ p₁ △ f₂ ∘ g₂ ∘ p₂

            ≈˘⟨ △-fuse ⟩
              (f₁ ∘ p₁ △ f₂ ∘ p₂) ∘ (g₁ ∘ p₁ △ g₂ ∘ p₂)
            ∎
          }
      }

    open Bifunctor -×- public
      using ()
      renaming
        ( Partialˡ to infix 40 -×_
        ; Partialʳ to infix 40 _×-
        )

    δ : ∀ {A} → A ⇒ A × A
    δ = id △ id

    open TerminalObject terminal public

    unitˡ : Fun 𝓒 𝓒 [ Id ≅ ⋆ ×- ] -- (natural isomorphism)
    unitˡ = record
      { _¹ = wrapNT record
          { α = ε △ id
          ; naturality = λ {A} {B} {f} →
              begin
                (ε △ id) ∘ f

              ≈⟨ △-dist ⟩
                ε ∘ f △ id ∘ f

              ≈⟨ △-resp-≈ ε-unique ∘-idˡ ⟩
                ε △ f

              ≈˘⟨ △-resp-≈ ∘-idˡ ∘-idʳ ⟩
                id ∘ ε △ f ∘ id

              ≈˘⟨ △-fuse ⟩
                (id ∘ p₁ △ f ∘ p₂) ∘ (ε △ id)
              ∎
          }

      -- TODO: this direction of naturality is extremely simple:
      -- rewrite this natural isomorphism as sym (natIso <this>)?
      ; _⁻¹ = wrapNT record
          { α = p₂
          ; naturality = △-factors-p₂
          }

      ; inverse = record
         { left-inverse = △-factors-p₂
         ; right-inverse = λ {A} →
             begin
               (ε △ id) ∘ p₂

             ≈⟨ △-dist ⟩
               ε ∘ p₂ △ id ∘ p₂

             ≈⟨ △-resp-≈ ε-unique ∘-idˡ ⟩
               ε △ p₂

             ≈˘⟨ △-resp-≈ˡ ε-unique ⟩
               p₁ △ p₂

             ≈⟨ △-η ⟩
               id
             ∎
         }
       }

    swap : -×- ⟹ Flip -×-
    swap = wrapNT record
      { α = p₂ △ p₁
      ; naturality = λ
          { {A₁ , A₂} {B₁ , B₂} {f₁ , f₂} →
              begin
                (p₂ △ p₁) ∘ (f₁ ∘ p₁ △ f₂ ∘ p₂)

              ≈⟨ △-dist ⟩
                p₂ ∘ (f₁ ∘ p₁ △ f₂ ∘ p₂) △ p₁ ∘ (f₁ ∘ p₁ △ f₂ ∘ p₂)

              ≈⟨ △-resp-≈ △-factors-p₂ △-factors-p₁ ⟩
                f₂ ∘ p₂ △ f₁ ∘ p₁

              ≈˘⟨ △-fuse ⟩
                (f₂ ∘ p₁ △ f₁ ∘ p₂) ∘ (p₂ △ p₁)
              ∎
          }
      }

    swap∘swap : ∀ {A B} → swap .α {A , B} ∘ swap .α ≈ id
    swap∘swap {A} {B} =
      begin
        (p₂ △ p₁) ∘ (p₂ △ p₁)

      ≈⟨ △-dist ⟩
        p₂ ∘ (p₂ △ p₁) △ p₁ ∘ (p₂ △ p₁)

      ≈⟨ △-resp-≈ △-factors-p₂ △-factors-p₁ ⟩
        p₁ △ p₂

      ≈⟨ △-η ⟩
        id
      ∎

    -×-×- : Functor (𝓒 ⨂ 𝓒 ⨂ 𝓒) 𝓒
    -×-×- = RightAssociated -×-

    [-×-]×- : Functor (𝓒 ⨂ 𝓒 ⨂ 𝓒) 𝓒
    [-×-]×- = LeftAssociated -×-

    assocˡ-α : ∀ {A B C} → A × B × C ⇒ (A × B) × C
    assocˡ-α = (p₁ △ p₁ ∘ p₂) △ p₂ ∘ p₂

    assocˡ-naturality
      : ∀ {A B} {f : 𝓒 ⨂ 𝓒 ⨂ 𝓒 [ A ⇒ B ]}
      → assocˡ-α ∘ -×-×- ₁ f ≈ [-×-]×- ₁ f ∘ assocˡ-α
    assocˡ-naturality {_} {_} {f₁ , f₂ , f₃} =
      △-unique′
        (begin _
         ≈⟨ ∘∘-resp-≈ˡ △-factors-p₁ ⟩ _
         ≈⟨ △-unique′ p₁≈p₁ p₂≈p₂ ⟩ _
         ≈˘⟨ ∘∘-resp-≈ʳ △-factors-p₁ ⟩ _
         ≈˘⟨ ∘∘-resp-≈ˡ △-factors-p₁ ⟩ _
         ∎)
        p₃≈p₃
     where
      p₁≈p₁
        : p₁ ∘ (p₁ △ p₁ ∘ p₂) ∘ -×-×- ₁ (f₁ , f₂ , f₃) ≈
            p₁ ∘ (f₁ ∘ p₁ △ f₂ ∘ p₂) ∘ (p₁ △ p₁ ∘ p₂)
      p₁≈p₁ =
        begin _
        ≈⟨ ∘∘-resp-≈ˡ △-factors-p₁ ⟩ _
        ≈⟨ △-factors-p₁ ⟩ f₁ ∘ p₁
        ≈˘⟨ ∘∘-resp-≈ʳ △-factors-p₁ ⟩ _
        ≈˘⟨ ∘∘-resp-≈ˡ △-factors-p₁ ⟩ _
        ∎

      p₂≈p₂
        : p₂ ∘ (p₁ △ p₁ ∘ p₂) ∘ (-×-×- ₁$ f₁ , f₂ , f₃) ≈
            p₂ ∘ (f₁ ∘ p₁ △ f₂ ∘ p₂) ∘ (p₁ △ p₁ ∘ p₂)
      p₂≈p₂ =
        begin p₂ ∘ (p₁ △ p₁ ∘ p₂) ∘ (-×-×- ₁$ f₁ , f₂ , f₃)
        ≈⟨ ∘∘-resp-≈ˡ △-factors-p₂ ⟩ _
        ≈⟨ ∘∘-resp-≈ʳ △-factors-p₂ ⟩ _
        ≈⟨ ∘∘-resp-≈ˡ △-factors-p₁ ⟩ _
        ≈⟨ ∘-assocʳ ⟩ f₂ ∘ p₁ ∘ p₂
        ≈˘⟨ ∘∘-resp-≈ʳ △-factors-p₂ ⟩ _
        ≈˘⟨ ∘∘-resp-≈ˡ △-factors-p₂ ⟩ _
        ∎

      p₃≈p₃
        : p₂ ∘ assocˡ-α ∘ -×-×- ₁ (f₁ , f₂ , f₃) ≈
            p₂ ∘ [-×-]×- ₁ (f₁ , f₂ , f₃) ∘ assocˡ-α
      p₃≈p₃ =
        begin _
        ≈⟨ ∘∘-resp-≈ˡ △-factors-p₂ ⟩ _
        ≈⟨ ∘∘-resp-≈ʳ △-factors-p₂ ⟩ _
        ≈⟨ ∘∘-resp-≈ˡ △-factors-p₂ ⟩ _
        ≈⟨ ∘-assocʳ ⟩ f₃ ∘ p₂ ∘ p₂
        ≈˘⟨ ∘∘-resp-≈ʳ △-factors-p₂ ⟩ _
        ≈˘⟨ ∘∘-resp-≈ˡ △-factors-p₂ ⟩ _
        ∎

    assocˡ-⟹ : RightAssociated -×- ⟹ LeftAssociated -×-
    assocˡ-⟹ = wrapNT record
      { α = assocˡ-α
      ; naturality = assocˡ-naturality
      }

    assocʳ-α : ∀ {A B C} → (A × B) × C ⇒ A × B × C
    assocʳ-α = p₁ ∘ p₁ △ p₂ ∘ p₁ △ p₂

    -- Just churn through evaluating all the projections to prove each
    -- element of the 3-tuple equal.
    assocʳ∘assocˡ : ∀ {A B C} → assocʳ-α {A} {B} {C} Retracts assocˡ-α
    assocʳ∘assocˡ =
      △-unique′ p₁≈p₁
        (≈.trans (∘∘-resp-≈ˡ △-factors-p₂)
          (△-unique′ p₂≈p₂ p₃≈p₃))
     where
      p₁≈p₁ : p₁ ∘ assocʳ-α ∘ assocˡ-α ≈ p₁ ∘ id
      p₁≈p₁ =
        begin _
        ≈⟨ ∘∘-resp-≈ˡ △-factors-p₁ ⟩ _
        ≈⟨ ∘∘-resp-≈ʳ △-factors-p₁ ⟩ _
        ≈⟨ △-factors-p₁ ⟩ p₁
        ≈˘⟨ ∘-idʳ ⟩ _
        ∎

      p₂≈p₂ : p₁ ∘ (p₂ ∘ p₁ △ p₂) ∘ assocˡ-α ≈ p₁ ∘ p₂ ∘ id
      p₂≈p₂ =
        begin _
        ≈⟨ ∘∘-resp-≈ˡ △-factors-p₁ ⟩ _
        ≈⟨ ∘∘-resp-≈ʳ △-factors-p₁ ⟩ _
        ≈⟨ △-factors-p₂ ⟩ p₁ ∘ p₂
        ≈˘⟨ ∘-resp-≈ʳ ∘-idʳ ⟩ _
        ∎

      p₃≈p₃ : p₂ ∘ (p₂ ∘ p₁ △ p₂) ∘ assocˡ-α ≈ p₂ ∘ p₂ ∘ id
      p₃≈p₃ =
        begin _
        ≈⟨ ∘∘-resp-≈ˡ △-factors-p₂ ⟩ _
        ≈⟨ △-factors-p₂ ⟩ p₂ ∘ p₂
        ≈˘⟨ ∘-resp-≈ʳ ∘-idʳ ⟩ _
        ∎

    assocˡ∘assocʳ : ∀ {A B C} → assocˡ-α {A} {B} {C} Retracts assocʳ-α
    assocˡ∘assocʳ =
      △-unique′
        (≈.trans (∘∘-resp-≈ˡ △-factors-p₁) -- Pre-simplify the shared p₁
          (△-unique′ p₁≈p₁ p₂≈p₂))
        p₃≈p₃
     where
      p₁≈p₁ : p₁ ∘ (p₁ △ p₁ ∘ p₂) ∘ assocʳ-α ≈ p₁ ∘ p₁ ∘ id
      p₁≈p₁ =
        begin _
        ≈⟨ ∘∘-resp-≈ˡ △-factors-p₁ ⟩ _
        ≈⟨ △-factors-p₁ ⟩ p₁ ∘ p₁
        ≈˘⟨ ∘-resp-≈ʳ ∘-idʳ ⟩ _
        ∎

      p₂≈p₂ : p₂ ∘ (p₁ △ p₁ ∘ p₂) ∘ assocʳ-α ≈ p₂ ∘ p₁ ∘ id
      p₂≈p₂ =
        begin _
        ≈⟨ ∘∘-resp-≈ˡ △-factors-p₂ ⟩ _
        ≈⟨ ∘∘-resp-≈ʳ △-factors-p₂ ⟩ _
        ≈⟨ △-factors-p₁ ⟩ p₂ ∘ p₁
        ≈˘⟨ ∘-resp-≈ʳ ∘-idʳ ⟩ _
        ∎

      p₃≈p₃ : p₂ ∘ assocˡ-α ∘ assocʳ-α ≈ p₂ ∘ id
      p₃≈p₃ =
        begin _
        ≈⟨ ∘∘-resp-≈ˡ △-factors-p₂ ⟩ _
        ≈⟨ ∘∘-resp-≈ʳ △-factors-p₂ ⟩ _
        ≈⟨ △-factors-p₂ ⟩ p₂
        ≈˘⟨ ∘-idʳ ⟩ _
        ∎

    assocˡ⁻¹ : ∀ {A} → Inverse (assocˡ-⟹ .α {A})
    assocˡ⁻¹ = record
      { f⁻¹ = assocʳ-α
      ; inverse = record
          { left-inverse = assocˡ∘assocʳ
          ; right-inverse = assocʳ∘assocˡ
          }
      }

    assoc : Fun _ _ [ RightAssociated -×- ≅ LeftAssociated -×- ]
    assoc = natIso _ _ assocˡ-⟹ assocˡ⁻¹

    monoidal : Monoidal 𝓒
    monoidal = record
      { 𝟏 = ⋆
      ; -⊗- = -×-
      ; assoc = wrapNatIso (unwrapNatIso assoc)
      ; unitˡ = unitˡ
      ; unitʳ = Core (Fun 𝓒 𝓒)
         [ record
             { _¹ = partialʳ⟹ swap _
             ; _⁻¹ = partialʳ⟹ (flip⟹ swap) _
               -- Somewhat annoyingly, we need a bunch of different inverse-y
               -- records that all use swap .α as their components and swap∘swap
               -- as their proofs, but they're not all interconvertible, and end
               -- up needing to be written in-line separately each time.
             ; inverse = record
                 { left-inverse = swap∘swap
                 ; right-inverse = swap∘swap
                 }
             }
         ∘ unitˡ
         ]
      }

    braided : Braided (bundle monoidal)
    braided = record
      { braiding = record
          { _¹ = swap .α
          ; _⁻¹ = swap .α
          ; inverse = record
              { left-inverse = swap∘swap
              ; right-inverse = swap∘swap
              }
          }
      ; naturality = λ
          { {A₁} {A₂} {B₁} {B₂} {f₁ , f₂} →
              begin
                (p₂ △ p₁) ∘ (f₁ ∘ p₁ △ f₂ ∘ p₂)

              ≈⟨ △-unique
                   (≈.trans (∘∘-resp-≈ˡ △-factors-p₁) △-factors-p₂)
                   (≈.trans (∘∘-resp-≈ˡ △-factors-p₂) △-factors-p₁) ⟩
                f₂ ∘ p₂ △ f₁ ∘ p₁

              ≈˘⟨ △-fuse ⟩
                (f₂ ∘ p₁ △ f₁ ∘ p₂) ∘ (p₂ △ p₁)
              ∎
          }
      }

    braidedMonoidal : BraidedMonoidal 𝓒
    braidedMonoidal = bundle braided

    -- Re-export some useful things derived from the monoidal
    -- category, while not re-exporting names derived from -⊗-, since
    -- -×- is preferred in the context of Cartesian categories.
    open BraidedMonoidal braidedMonoidal public
      using (assocˡ; assocʳ; braid)

    symmetric : Symmetric (bundle braidedMonoidal)
    symmetric = record { braid-involutive = swap∘swap }

record CartesianCategory (o m ℓ : Level) : Set (suc (o ⊔ m ⊔ ℓ)) where
  constructor bundle
  field
    {𝓤} : Category o m ℓ
    cartesian : Cartesian 𝓤

  open Category 𝓤 public
  open Cartesian cartesian public

  monoidalCategory : MonoidalCategory o m ℓ
  monoidalCategory = bundle monoidal

  braidedMonoidalCategory : BraidedMonoidalCategory o m ℓ
  braidedMonoidalCategory = bundle braidedMonoidal
