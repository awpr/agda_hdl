open import Categories.Category using (Category)

module Categories.Coalgebra {o m ℓ} {𝓒 : Category o m ℓ} where

open import Data.Unit using (⊤; tt)
open import Level using (Level; _⊔_)
open import Function using (_on_)

open import Categories.Functor using (Functor)

open Categories.Functor.FunctorOperators
open Category 𝓒

private
  variable
    F : Functor 𝓒 𝓒

record Coalgebra (F : Functor 𝓒 𝓒) : Set (o ⊔ m) where
  field
    {Carrier} : Obj
    step : Carrier ⇒ F ₀ Carrier

record CoalgebraMorphism (A B : Coalgebra F) : Set (m ⊔ ℓ) where
  private
    module A = Coalgebra A
    module B = Coalgebra B

  field
    action : A.Carrier ⇒ B.Carrier

    -- Stubbed out for now: lacking the required properties of
    -- categories to allow proving it.
    action-resp-coalg : (λ _ → ⊤) (B.step ∘ action ≈ F ₁ action ∘ A.step)

Coalg : Functor 𝓒 𝓒 → Category (o ⊔ m) (m ⊔ ℓ) ℓ
Coalg F = record
  { Obj = Coalgebra F
  ; _⇒_ = CoalgebraMorphism
  ; _≈_ = _≈_ on CoalgebraMorphism.action -- Ignore the equivalence component
  ; id = record { action = id ; action-resp-coalg = tt }
  ; _∘_ = λ f g → record
    { action = CoalgebraMorphism.action f ∘ CoalgebraMorphism.action g
    ; action-resp-coalg = tt
    }
  ; equiv = record { refl = ≈.refl ; sym = ≈.sym ; trans = ≈.trans}
  ; ∘-resp-≈ = ∘-resp-≈
  ; ∘-idˡ = ∘-idˡ
  ; ∘-idʳ = ∘-idʳ
  ; ∘-assocˡ = ∘-assocˡ
  }
