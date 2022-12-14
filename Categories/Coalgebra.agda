open import Categories.Category using (Category)

module Categories.Coalgebra {o m â} {ð : Category o m â} where

open import Data.Unit using (â¤; tt)
open import Level using (Level; _â_)
open import Function using (_on_)

open import Categories.Functor using (Functor)

open Categories.Functor.FunctorOperators
open Category ð

private
  variable
    F : Functor ð ð

record Coalgebra (F : Functor ð ð) : Set (o â m) where
  field
    {Carrier} : Obj
    step : Carrier â F â Carrier

record CoalgebraMorphism (A B : Coalgebra F) : Set (m â â) where
  private
    module A = Coalgebra A
    module B = Coalgebra B

  field
    action : A.Carrier â B.Carrier

    -- Stubbed out for now: lacking the required properties of
    -- categories to allow proving it.
    action-resp-coalg : (Î» _ â â¤) (B.step â action â F â action â A.step)

Coalg : Functor ð ð â Category (o â m) (m â â) â
Coalg F = record
  { Obj = Coalgebra F
  ; _â_ = CoalgebraMorphism
  ; _â_ = _â_ on CoalgebraMorphism.action -- Ignore the equivalence component
  ; id = record { action = id ; action-resp-coalg = tt }
  ; _â_ = Î» f g â record
    { action = CoalgebraMorphism.action f â CoalgebraMorphism.action g
    ; action-resp-coalg = tt
    }
  ; equiv = record { refl = â.refl ; sym = â.sym ; trans = â.trans}
  ; â-resp-â = â-resp-â
  ; â-idË¡ = â-idË¡
  ; â-idÊ³ = â-idÊ³
  ; â-assocË¡ = â-assocË¡
  }
