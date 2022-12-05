{-# OPTIONS --safe #-}

module Categories.Category.Types where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Function using (id; _∘′_; _$_)
open import Level using (suc; Lift; lift)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≗_; _→-setoid_)

open import Categories.Braided using (Braided)
open import Categories.Cartesian using (Cartesian; CartesianCategory)
open import Categories.CartesianClosed using (CartesianClosed)
open import Categories.Category using (Category)
open import Categories.ClosedMonoidal using (LeftClosed)
open import Categories.Monoidal using (Monoidal)
open import Categories.Terminal using (TerminalObject)

→Cat : ∀ ℓ → Category (suc ℓ) ℓ ℓ
→Cat ℓ = record
  { Obj = Set ℓ
  ; _⇒_ = λ A B → A → B
  ; _≈_ = _≗_
  ; id = id
  ; _∘_ = _∘′_
  ; equiv = λ {A B} → Setoid.isEquivalence (A →-setoid B)

  ; ∘-resp-≈ =
      λ {A} {B} {C} {f₁} {f₂} f₁≗f₂ g₁≗g₂ x → ≡.trans (f₁≗f₂ _) (≡.cong f₂ (g₁≗g₂ x))
  ; ∘-idˡ = λ _ → ≡.refl
  ; ∘-idʳ = λ _ → ≡.refl
  ; ∘-assocˡ = λ _ → ≡.refl
  }

ε-unique : ∀ {a b} {A : Set a} {f : A → Lift b ⊤} (x : A) → f x ≡.≡ lift tt
ε-unique {f = f} x with lift tt ← f x = ≡.refl

module _ {ℓ} where
  term→ : TerminalObject (→Cat ℓ)
  term→ = record
    { ⋆ = Lift _ ⊤
    ; ε = λ _ → lift tt
    ; ε-unique = ε-unique
    }

  cart→ : Cartesian (→Cat ℓ)
  cart→ = record
    { terminal = term→
    ; _×_ = _×_
    ; _△_ = λ f g x → f x , g x
    ; p₁ = proj₁
    ; p₂ = proj₂
    ; △-factors-p₁ = λ x → ≡.refl
    ; △-factors-p₂ = λ x → ≡.refl
    ; △-unique = λ f≗f g≗g x → ≡.cong₂ _,_ (f≗f x) (g≗g x)
    }

module _ ℓ where
  →CC : CartesianCategory (suc ℓ) ℓ ℓ
  →CC = record { 𝓤 = →Cat ℓ ; cartesian = cart→ }

  open CartesianCategory →CC
    using ()
    renaming (braidedMonoidalCategory to →BMC; monoidalCategory to →MC)
    public

module _ {ℓ} where
  -- →CC but with its Level argument inferred.
  →CC′ : CartesianCategory (suc ℓ) ℓ ℓ
  →CC′ = →CC ℓ

  open CartesianCategory (→CC ℓ)
    using ()
    renaming (braided to braid→; monoidal to mon→)
    public
