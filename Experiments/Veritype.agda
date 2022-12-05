module Experiments.Veritype where

open import Data.List using (List; _∷_; []; _++_)
open import Data.List.Relation.Unary.All as All using (All; _∷_; [])
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.Any.Properties as Any
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_×_; _,_; -,_; ∃-syntax)
open import Data.String using (String)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Level using (zero; _⊔_)
open import Function using (case_of_; _$_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Categories.Bicartesian using (Bicartesian)
open import Categories.Category using (Category)
open import Categories.Cartesian using (Cartesian)
open import Categories.Coproducts using (Coproducts)
open import Categories.Distributive using (Distributive; DistributiveCategory; bundle)
open import Categories.Terminal using (TerminalObject)

data Type : Set where
  -- Want to see that built-in primitive types can play well with the
  -- rest of the system.
  bit : Type

  𝟏 : Type
  _⊗_ : Type → Type → Type

  ⊥ : Type
  _⊎_ : Type → Type → Type

Product : List Type → Type
Product [] = 𝟏
Product (x ∷ xs) = x ⊗ Product xs

data Selection {a} {A : Set a} : (xs ys : List A) → Set where
  keep : ∀ {x xs ys} → Selection xs ys → Selection (x ∷ xs) (x ∷ ys)
  drop : ∀ {x xs ys} → Selection xs ys → Selection (x ∷ xs) ys
  done : Selection [] []

_∘ₛ_
  : ∀ {a} {A : Set a} {xs ys zs : List A}
  → Selection ys zs → Selection xs ys → Selection xs zs
f ∘ₛ drop g = drop (f ∘ₛ g)
drop f ∘ₛ keep g = drop (f ∘ₛ g)
keep f ∘ₛ keep g = keep (f ∘ₛ g)
done ∘ₛ done = done

idₛ : ∀ {a} {A : Set a} {xs : List A} → Selection xs xs
idₛ {xs = []} = done
idₛ {xs = _ ∷ _} = keep idₛ

-- Terminal morphism of Selections.
εₛ : ∀ {a} {A : Set a} {xs : List A} → Selection xs []
εₛ {xs = []} = done
εₛ {xs = _ ∷ _} = drop εₛ

-- Projections of the product (concatenation) of Selections.
p₁ₛ : ∀ {a} {A : Set a} {xs ys : List A} → Selection (xs ++ ys) xs
p₁ₛ {xs = []} = εₛ
p₁ₛ {xs = _ ∷ _} = keep p₁ₛ

p₂ₛ : ∀ {a} {A : Set a} {xs ys : List A} → Selection (xs ++ ys) ys
p₂ₛ {xs = []} = idₛ
p₂ₛ {xs = _ ∷ _} = drop p₂ₛ

data Partition {a} {A : Set a} : (xs ys zs : List A) → Set where
  left : ∀ {x xs ys zs} → Partition xs ys zs → Partition (x ∷ xs) (x ∷ ys) zs
  right : ∀ {x xs ys zs} → Partition xs ys zs → Partition (x ∷ xs) ys (x ∷ zs)
  both : ∀ {x xs ys zs} → Partition xs ys zs → Partition (x ∷ xs) (x ∷ ys) (x ∷ zs)
  done : Partition [] [] []

copy : ∀ {a} {A : Set a} {xs : List A} → Partition xs xs xs
copy {xs = []} = done
copy {xs = _ ∷ _} = both copy

lefts
  : ∀ {a} {A : Set a} {xs ys zs : List A}
  → Partition xs ys zs → Selection xs ys
lefts (left x) = keep (lefts x)
lefts (right x) = drop (lefts x)
lefts (both x) = keep (lefts x)
lefts done = done

rights
  : ∀ {a} {A : Set a} {xs ys zs : List A}
  → Partition xs ys zs → Selection xs zs
rights (left x) = drop (rights x)
rights (right x) = keep (rights x)
rights (both x) = keep (rights x)
rights done = done

onLeft
  : ∀ {a} {A : Set a} {xs ys : List A}
  → Selection xs ys → Partition xs ys xs
onLeft (keep x) = both (onLeft x)
onLeft (drop x) = right (onLeft x)
onLeft done = done

factor
  : ∀ {a} {A : Set a} {xs ys zs : List A}
  → Selection xs ys
  → Selection xs zs
  → ∃[ xs′ ] (Selection xs xs′ × Partition xs′ ys zs)
factor (keep ys) (keep zs) =
  let _ , sxs , yzs = factor ys zs
  in  -, keep sxs , both yzs
factor (keep ys) (drop zs) =
  let _ , sxs , yzs = factor ys zs
  in  -, keep sxs , left yzs
factor (drop ys) (keep zs) =
  let _ , sxs , yzs = factor ys zs
  in  -, keep sxs , right yzs
factor (drop ys) (drop zs) =
  let _ , sxs , yzs = factor ys zs
  in  -, drop sxs , yzs
factor done done = [] , done , done

record Partition₃ {a} {A : Set a} (xs ys zs ws : List A) : Set a where
  field
    {zws} : List A
    par₁ : Partition xs ys zws
    par₂ : Partition zws zs ws

infix 10 _⇑_
record _⇑_ {a b} {A : Set a} (B : List A → Set b) (xs : List A) : Set (a ⊔ b) where
  constructor _↑_
  field
    {ys} : List A
    val : B ys
    support : Selection xs ys

weaken
  : ∀ {a b} {A : Set a} {B : List A → Set b} {xs ys : List A}
  → Selection xs ys → B ⇑ ys → B ⇑ xs
weaken sel (b ↑ sel₂) = b ↑ (sel₂ ∘ₛ sel)

-- Covering pairs, as in "Everybody's got to be somewhere"
infixr 20 _∏_
infixr 20 _⟩_⟨_
record _∏_
    {a b c} {A : Set a}
    (B : List A → Set b)
    (C : List A → Set c)
    (xs : List A)
    : Set (a ⊔ b ⊔ c) where
  constructor _⟩_⟨_
  field
    {ys zs} : List A
    proj₁ : B ys
    par : Partition xs ys zs
    proj₂ : C zs

infixr 20 _,,_
pattern _,,_ x y = x ⟩ _ ⟨ y

-- Construction of covering pairs by `factor`.
_&_
  : ∀ {a b c} {A : Set a}
      {B : List A → Set b}
      {C : List A → Set c}
      {xs : List A}
  → B ⇑ xs
  → C ⇑ xs
  → B ∏ C ⇑ xs
(b ↑ sb) & (c ↑ sc) =
  let _ , sel , par = factor sb sc
  in  (b ⟩ par ⟨ c) ↑ sel

record Binder
    {a b} {A : Set a}
    (ys : List A)
    (B : List A → Set b)
    (xs : List A)
    : Set (a ⊔ b) where
  field
    {zs} : List A
    sel : Selection ys zs
    val : B (zs ++ xs)

Binder₁ : ∀ {a b} {A : Set a} → A → (List A → Set b) → List A → Set (a ⊔ b)
Binder₁ A = Binder (A ∷ [])

data Term : Type → List Type → Set where
  var : ∀ {A} → Term A (A ∷ [])

  𝟎 : Term bit []
  𝟏 : Term bit []
  if-then-else
    : ∀ {Γ A}
    → (Term bit ∏ Term A ∏ Term A) Γ
    → Term A Γ

  tt : Term 𝟏 []
  -- Product introduction: given terms for each factor, they can be
  -- combined into a product term.
  pair
    : ∀ {A B Γ}
    → (Term A ∏ Term B) Γ
    → Term (A ⊗ B) Γ

  -- Product elimination: given a term in a context augmented by the
  -- factors, satisfy the additional bindings using the factors of a
  -- product.  This is more akin to a linear-logic product elimination
  -- rule than than the traditional projections, and also more akin to
  -- the natural pattern-match on the n-ary product.  To recover
  -- projections, combine this with `var`.
  π
    : ∀ {A B C Γ}
    → (Term (A ⊗ B) ∏ Binder (A ∷ B ∷ []) (Term C)) Γ
    → Term C Γ

  absurd : ∀ {A Γ} → Term ⊥ Γ → Term A Γ
  inj₁ : ∀ {A B Γ} → Term A Γ → Term (A ⊎ B) Γ
  inj₂ : ∀ {A B Γ} → Term B Γ → Term (A ⊎ B) Γ
  either
    : ∀ {A B C Γ}
    → (Term (A ⊎ B) ∏ Binder₁ A (Term C) ∏ Binder₁ B (Term C)) Γ
    → Term C Γ

{-
weaken-++ : ∀ {Γ Δ Φ} {A : Type} → (∀ {A} → A ∈ Γ → A ∈ Δ) → A ∈ Φ ++ Γ → A ∈ Φ ++ Δ
weaken-++ {Φ = Φ} f A∈Φ++Γ = case Any.++⁻ Φ A∈Φ++Γ of λ where
  (inj₁ A∈Φ) → Any.++⁺ˡ A∈Φ
  (inj₂ A∈Γ) → Any.++⁺ʳ Φ (f A∈Γ)

-- Even though in principle we could recover `weaken` from the below
-- form of `subst` by re-wrapping `var`s, the termination checker
-- isn't smart enough to figure out that this terminates, so we need
-- the specialization spelled out explicitly.
weaken : ∀ {Γ Δ A} → (∀ {B} → B ∈ Γ → B ∈ Δ) → Term Γ A → Term Δ A
weaken f (var x) = var (f x)
weaken f 𝟎 = 𝟎
weaken f 𝟏 = 𝟏
weaken f (if x then y else z) = if weaken f x then weaken f y else weaken f z
weaken {Γ} {Δ} f (Π xs) = Π (go xs)
  where
    -- Termination checker needs hand-holding, so we can't just `All.map`
    go : ∀ {Φ} → All (Term Γ) Φ → All (Term Δ) Φ
    go [] = []
    go (x ∷ xs) = weaken f x ∷ go xs
weaken f (π {Δ} x y) = π (weaken f x) (weaken (weaken-++ f) y)
weaken f (absurd x) = absurd (weaken f x)
weaken f (inj₁ x) = inj₁ (weaken f x)
weaken f (inj₂ x) = inj₂ (weaken f x)
weaken f (either x y z) =
  either
    (weaken f x)
    (weaken (weaken-++ f) y)
    (weaken (weaken-++ f) z)

subst-++ : ∀ {Γ Δ Φ A} → (∀ {B} → B ∈ Γ → Term Δ B) → A ∈ Φ ++ Γ → Term (Φ ++ Δ) A
subst-++ {Φ = Φ} f A∈Φ++Γ = case Any.++⁻ Φ A∈Φ++Γ of λ where
  (inj₁ A∈Φ) → var (Any.++⁺ˡ A∈Φ)
  (inj₂ A∈Γ) → weaken (Any.++⁺ʳ Φ) (f A∈Γ)

subst : ∀ {Γ Δ A} → (∀ {B} → B ∈ Γ → Term Δ B) → Term Γ A → Term Δ A
subst f (var x) = f x
subst f 𝟎 = 𝟎
subst f 𝟏 = 𝟏
subst f (if x then y else z) = if subst f x then subst f y else subst f z
subst {Γ} {Δ} f (Π xs) = Π (go xs)
  where
    go : ∀ {Φ} → All (Term Γ) Φ → All (Term Δ) Φ
    go [] = []
    go (x ∷ xs) = subst f x ∷ go xs
subst f (π {Φ} x y) = π (subst f x) (subst (subst-++ f) y)
subst f (absurd x) = absurd (subst f x)
subst f (inj₁ x) = inj₁ (subst f x)
subst f (inj₂ x) = inj₂ (subst f x)
subst f (either x y z) =
  either
    (subst f x)
    (subst (subst-++ f) y)
    (subst (subst-++ f) z)

-- TODO: rewrite the following to describe what's actually chosen,
-- once things are more settled.

-- `Module` is the thing that will ultimately be either rendered to a
-- Verilog source module or further composed and simplified.  That
-- means we'll need a way to obtain variable names for both the inputs
-- and outputs of a morphism.  When intermediate signals are shared,
-- they'll also need names; when they're unshared or discarded, they
-- can be inlined/dropped, so names won't be strictly necessary.
-- Associating name labels with each `All (Term Γ) Δ` binding-group
-- will provide names for outputs and intermediate values, but not for
-- inputs.  Presumably that means we'll need to represent input names
-- separately at the top level.  Alternatively, have each "tier"
-- represent its input names, and additionally provide output names in
-- `done`?
--
-- How to approach the double-specification of names when composing
-- morphisms?  If morphisms (modules) provide name labels for both
-- their inputs and outputs, then the intermediates of a composite
-- morphism potentially have two candidate names; which do we prefer?
-- The resulting composite will be like `let-in <lhs> (done <rhs>)`.
-- What will the Agda-side source look like?  Presumably there will be
-- a pragmatically-focused CT abstraction for categories that can
-- attach labels to their "wires".  Then bindings will look like `x ←
-- label "x" something` for intermediates.  What about function
-- inputs?  Well, there's already a slightly-awkward convention to
-- `let-in` function parameters, so they can be the same: `x ← label
-- "x" x′`.  By that convention, functions' inputs would naturally be
-- labeled, but not their outputs.  Perhaps when defining things meant
-- to be synthesized directly, labels would be attached intentionally
-- to outputs as well.  So, then, in practice, only function
-- parameters would typically have labels, and competing specified
-- labels would only appear when composing something with a module
-- having name labels on its outputs.  When they do appear, it'd be as
-- the composite of two labeling morphisms.  A labeling morphism would
-- be an identity substitution having an output label (and maybe also
-- an input label?).  Composition would then need to choose one or the
-- other for the intermediate, or substitute/simplify it away, and the
-- most natural result would be an identity morphism with different
-- input and output labels.  Composing (and simplifying) this further
-- would naturally mean substituting away one name or the other,
-- according to which side the composition is on.
--
-- How does this interact with the presheaf category machinery?  The
-- translation of "apply a function" is to compose a morphism on the
-- left, so `label "x" x` would be `label_ "x" ∘ x`.  Then `label_` is
-- just an identity morphism with a label attached.  `x` there would
-- be any morphism from context to value: often just a variable
-- reference, but perhaps a complex term.  This would then be given to
-- `let-in` to implement sharing.  That in turn means composing the
-- rest of the circuit with `id △ (label "x" ∘ x)`, which should
-- result in either a preserved `let-in` constructor assigning "x" to
-- the given term or a simplified composite that has no "x" at all.
--
-- There seems to be a need for a notion of how strongly desired a
-- name is: we might want to provide a name only where it's
-- structurally necessary as a fallback for inlining the subterm, or
-- we might wish to force a subterm to be rendered as a Verilog
-- binding and insist that it have a given name.  This could also
-- control what happens when two name assignments contradict: the
-- strongest preference wins.

{-
-- A typed term associated with an optional, semantically-irrelevant
-- name, for display / readability purposes.
record Binding (Γ : List Type) (A : Type) : Set where
  constructor binding
  field
    name : Maybe String
    term : Term Γ A

open Binding

overTerm : ∀ {Γ Δ A B} → (Term Γ A → Term Δ B) → Binding Γ A → Binding Δ B
overTerm f b = record { name = b .name ; term = f (b .term) }

anon : ∀ {Γ A} → Term Γ A → Binding Γ A
anon x = record { name = nothing ; term = x }

named : ∀ {Γ A} → String → Term Γ A → Binding Γ A
named nm x = record { name = just nm ; term = x }

anons : ∀ {Γ Δ} → All (Term Γ) Δ → All (Binding Γ) Δ
anons = All.map anon

tabulateAnon : ∀ {Γ Δ} → (∀ {A} → A ∈ Δ → Term Γ A) → All (Binding Γ) Δ
tabulateAnon f = All.tabulate (λ x → anon (f x))
-}

weaken* : ∀ {Γ Δ Φ} → (∀ {A} → A ∈ Γ → A ∈ Φ) → All (Term Γ) Δ → All (Term Φ) Δ
weaken* f = All.map (weaken f)

allVars : ∀ {Γ} → All (Term Γ) Γ
allVars = All.tabulate var
-}

termSize : ∀ {Γ A} → Term Γ A → ℕ
termSize var = 1
termSize 𝟎 = 1
termSize 𝟏 = 1
termSize (if-then-else (x ,, y ,, z)) = 1 + termSize x + termSize y + termSize z
termSize tt = 1
termSize (pair (x ⟩ _ ⟨ y)) = 1 + termSize x + termSize y
termSize (π (x ,, y)) = 1 + termSize x + termSize (y .Binder.val)
termSize (absurd x) = 1 + termSize x
termSize (inj₁ x) = 1 + termSize x
termSize (inj₂ x) = 1 + termSize x
termSize (either (x ,, y ,, z)) =
  1 + termSize x + termSize (y .Binder.val) + termSize (z .Binder.val)

record Module (Γ Δ : List Type) : Set where
  field
    body : ∀ {A Φ} → (∀ {Ψ} → Partition Ψ Δ Φ → Term A ⇑ Ψ) → Selection Φ Γ → Term A ⇑ Φ

open Module

{-
-- Construct a module from individual terms for each of its factors.
fromTerms : ∀ {Γ Δ} → All (Term Γ) Δ → Module Γ Δ
fromTerms xs = record { body = Π xs }

fromTerm : ∀ {Γ A} → Term Γ A → Module Γ (A ∷ [])
fromTerm x = fromTerms (x ∷ [])
-}

id : ∀ {Γ} → Module Γ Γ
id = record { body = λ f sel → f (onLeft sel) }

_∘_ : ∀ {Γ Δ Φ} → Module Δ Φ → Module Γ Δ → Module Γ Φ
f ∘ g = record
  { body = λ x sel →
      g .body
        (λ Ψ₁ΔΦ →
          f .body
            (λ ΨΦΨ₁ →
                 let Ξ , Ψ₁Ξ , ΞΦΦ₁ = factor (lefts ΨΦΨ₁) (rights Ψ₁ΔΦ ∘ₛ rights ΨΦΨ₁)
                 in  weaken Ψ₁Ξ (x ΞΦΦ₁))
            (lefts Ψ₁ΔΦ))
        sel
  }

{-
_++ₐ_
  : ∀ {a ℓ} {A : Set a} {P : A → Set ℓ} {xs ys : List A}
  → All P xs → All P ys → All P (xs ++ ys)
[] ++ₐ Pys = Pys
(Px ∷ Pxs) ++ₐ Pys = Px ∷ (Pxs ++ₐ Pys)

appendₐ
  : ∀ {a ℓ} {A : Set a} {P : A → Set ℓ} (xs : List A) {ys : List A}
  → All P xs → All P ys → All P (xs ++ ys)
appendₐ _ Pxs Pys = Pxs ++ₐ Pys

over++ʳ
  : ∀ {a} {A : Set a} {Γ Δ Φ : List A}
  → (∀ {x} → x ∈ Γ → x ∈ Δ) → ∀ {x} → x ∈ Φ ++ Γ → x ∈ Φ ++ Δ
over++ʳ {Φ = Φ} f A∈Φ++Γ = case Any.++⁻ Φ A∈Φ++Γ of λ where
  (inj₁ A∈Φ) → Any.++⁺ˡ A∈Φ
  (inj₂ A∈Γ) → Any.++⁺ʳ Φ (f A∈Γ)

nothings : ∀ {a} {A : Set a} {xs : List A} → All (λ _ → Maybe String) xs
nothings = All.tabulate (λ _ → nothing)

mergeName : (x y : Maybe String) → Maybe String
mergeName (just x) _ = just x
mergeName nothing  y = y

mergeNames
  : ∀ {a} {A : Set a} {Γ : List A}
  → (xs ys : All (λ _ → Maybe String) Γ)
  → All (λ _ → Maybe String) Γ
mergeNames xs ys = All.zipWith (λ (x , y) → mergeName x y) (xs , ys)
-}

-- Stubbed-out equivalence relation for the time being, to make it
-- possible to connect this to existing circuit definitions before
-- fulfilling all the proof obligations.  In particular, this means
-- the category itself needn't have proofs of any nontrivial
-- equivalences between its morphisms, functors into the category
-- won't be required to uphold any meaningful functoriality
-- conditions, and functors out of the category generally won't be
-- possible (because all morphisms are equivalent, any functors out of
-- the category must be degenerate).
_≈_ : ∀ {Γ Δ} → (f g : Module Γ Δ) → Set
f ≈ g = ⊤

_△_ : ∀ {Γ Δ Φ} → Module Γ Δ → Module Γ Φ → Module Γ (Δ ++ Φ)
f △ g = record
  { body = λ x sel →
      f .body
      (λ ΨΔΦ →
        g .body
          -- End of day notes Nov 30: `x` here wants an environment
          -- where `Δ` is specifically before `Φ₁`, but we haven't
          -- guaranteed that; we can either introduce cruft to put
          -- things in the expected order, or introduce permutation to
          -- the logic, or come up with some other solution.
          (λ Ψ₁Φ₁Ψ → x {!!})
          (sel ∘ₛ rights ΨΔΦ))
      sel
  }

{-
_△_ : ∀ {Γ Δ Φ} → Module Γ Δ → Module Γ Φ → Module Γ (Δ ++ Φ)
_△_ {Γ} {Δ} {Φ} f g = record
  { body = π (g .body) (π (weaken (Any.++⁺ʳ Φ) (f .body)) (weaken w (Π allVars)))
  }
  where
  w : ∀ {A} → A ∈ Δ ++ Φ → A ∈ Δ ++ Φ ++ Γ
  w A∈Δ++Φ = case Any.++⁻ Δ A∈Δ++Φ of λ where
    (inj₁ A∈Δ) → Any.++⁺ˡ A∈Δ
    (inj₂ A∈Φ) → Any.++⁺ʳ Δ (Any.++⁺ˡ A∈Φ)
-}

{-
p₁ : ∀ {Γ Δ} → Module (Γ ++ Δ) Γ
p₁ = record { body = λ (x ↑ sel) → x ↑ (sel ∘ₛ p₁ₛ) }

p₂ : ∀ {Γ Δ} → Module (Γ ++ Δ) Δ
p₂ {Γ} = record { body = λ (x ↑ sel) → x ↑ (sel ∘ₛ p₂ₛ {xs = Γ}) }
-}

{-
_∐_ : List Type → List Type → List Type
Γ ∐ Δ = (Π Γ ⊎ Π Δ) ∷ []

_▽_ : ∀ {Γ Δ Φ} → Module Γ Φ → Module Δ Φ → Module (Γ ∐ Δ) Φ
f ▽ g = record
  { body = either var₀
      (π var₀ (weaken Any.++⁺ˡ (f .body)))
      (π var₀ (weaken Any.++⁺ˡ (g .body)))
  }

module Modules where
  category : Category zero zero zero
  category = record
    { Obj = List Type
    ; _⇒_ = Module
    ; _≈_ = _≈_
    ; id = id
    ; _∘_ = _∘_
    ; equiv = record { refl = tt ; sym = λ _ → tt ; trans = λ _ _ → tt }
    ; ∘-resp-≈ = λ _ _ → tt
    ; ∘-idˡ = tt
    ; ∘-idʳ = tt
    ; ∘-assocˡ = tt
    }

  terminal : TerminalObject category
  terminal = record
    { ⋆ = []
    ; ε = fromTerms []
    ; ε-unique = tt
    }

  cartesian : Cartesian category
  cartesian = record
    { terminal = terminal
    ; _×_ = _++_
    ; _△_ = _△_
    ; p₁ = p₁
    ; p₂ = p₂
    ; △-factors-p₁ = tt
    ; △-factors-p₂ = tt
    ; △-unique = λ _ _ → tt
    }

  coproducts : Coproducts category
  coproducts = record
    { _∐_ = _∐_
    ; ⊥ = ⊥ ∷ []
    ; ∃! = fromTerms (All.tabulate (λ _ → absurd var₀))
    ; i₁ = fromTerm (inj₁ (Π allVars))
    ; i₂ = fromTerm (inj₂ (Π allVars))
    ; _▽_ = _▽_
    ; ▽-resp-≈ = λ _ _ → tt
    }

  bicartesian : Bicartesian category
  bicartesian = record { cartesian = cartesian ; coproducts = coproducts }

  distributive : Distributive category
  distributive = record
    { bicartesian = bicartesian
    ; distʳ = λ {Γ} {Δ} {Φ} → record
        { f⁻¹ = fromTerm $
            either var₀
              (inj₁ (π var₀ (Π
                (appendₐ Γ
                  (weaken* Any.++⁺ˡ allVars)
                  (weaken* (λ A∈Δ → Any.++⁺ʳ Γ (Any.++⁺ʳ (_ ∷ _ ∷ []) A∈Δ)) allVars)))))
              (inj₂ (π var₀ (Π
                (appendₐ Φ
                  (weaken* Any.++⁺ˡ allVars)
                  (weaken* (λ A∈Δ → Any.++⁺ʳ Φ (Any.++⁺ʳ (_ ∷ _ ∷ []) A∈Δ)) allVars)))))
        }
    }

Modules : DistributiveCategory zero zero zero
Modules = bundle Modules.distributive

-- Nov 21 notes: trying to address the problem of massive modules
-- being created for even relatively simple circuits.
--
-- This bloat comes from everything being done in the context of an
-- ever-increasing environment, and needing to name all the variables
-- to be preserved even in simple cases of structural manipulation
-- like `id` and `p₂`.
--
-- We could try to simplify it away after constructing the
-- unsimplified term, but this means churning through a
-- seemingly-cubic amount of data in the number of `←`s.
--
-- We could try to simplify it incrementally every step of the way
-- (e.g. by keeping track of the occurrence count of each variable in
-- each morphism and substituting away linear bindings), but that
-- still appears to be a cubic amount of work.
--
-- We could try to target specific cases where needless variable
-- manipulation happens, like in `f ∘ (x △ id)`, by adding a `let-in`
-- field for the whole composite to the Cartesian record, but that
-- doesn't address other cases like `f ∘ p₂`.
--
-- It might be desirable to find some way to prune the environment as
-- we go, but I don't know how that would work, since the convenience
-- of being able to reference any in-scope variable at any time seems
-- to be at odds with the more-global knowledge of what variables are
-- used within a particular subterm.
--
-- I have a hunch that working with copresheaves might be helpful
-- somehow, since then morphisms would be like `∀ {A} → Module Δ A →
-- Module Γ A`, which might allow for simpler, more efficient
-- interpretations of towers of composed projections: then projections
-- are weakening functions (or even weakening _constructors_).  Note
-- that if projection is a weakening _pass_, this would result in a
-- separate weakening pass for each composed projection, so it looks
-- pretty expensive, too, and weakening constructors would end up
-- being essentially required.
--
-- Finally, can I come up with a different presentation of the logic
-- that doesn't suffer from this collection of problems in the first
-- place?
--
-- Nov 22:
--
-- The "copresheaves" setup (note: is it actually copreasheaves?  yes,
-- the embedding of Γ would be `λ Δ → Module Γ Δ` -- although we'd be
-- looking at the opposite of the copresheaf category) does help to
-- paper over the difference of symmetry between CT and logic.  It
-- does present an opportunity for the composition of many `p₂`s to
-- normalize quickly to a module with minimal cruft, since `p₂`
-- becomes a function that just prepends a few "zeros" onto the
-- thinning at the top of a module (assuming the Conor McBride
-- "everyone's gotta go somewhere" style of co-de-Bruijn indices).
-- Similarly `id` can be an actual identity function and cost ~nothing
-- (compare to the `id` of the underlying `Modules` category, which is
-- linear in the number of bindings in the context).
--
-- This does also allow for an efficient `x △ id` morphism to exist
-- (namely, `λ f → π (Π x) f` a.k.a. `let-in x f`), but I haven't
-- figured out yet how _△_ is implemented or whether that will
-- naturally produce an efficient `x △ id`.  EOD answer: seems like
-- it's not efficient, unless I'm missing something: _△_ ends up
-- needing to use the underlying `id` for each side of the product,
-- which is fine when "constructing tuples", but is problematic when
-- "augmenting the environment".
--
-- Does p₁ work nicely?  Seems not so bad: it has to construct a
-- bit-vector of zeros for the tail of the context, but that doesn't
-- need further processing -- it just becomes part of the binding
-- structure.
--
-- Does the co-de-Bruijn representation lend itself to emitting code?
-- That is the whole point, after all.  It seems like it should work
-- just as well: instead of plucking a variable name out of an
-- ever-growing naming environment, it'd iteratively prune the naming
-- environment down until only a single name remains at each leaf, and
-- then emit that name.
--
-- Note apropos of nothing: there would appear to be a conflict
-- between Verilog's lack of lightweight unnamed tuples and the
-- logic's n-ary product construction, but in fact I think that's
-- solved by having the code-emitting implementation take a collection
-- of names to assign the output's components to: then the top-level
-- structure of a module, the intermediate let-binding, the arms of an
-- `either`, and the contents of a sequential loop can all be handled
-- by the same mechanism.
--
-- Another note apropos of nothing: if I end up going to a "Verilog
-- syntax data structure" rather than directly to text, it might make
-- sense to defer assigning the final signal names until after that
-- data structure, to simplify the conversion.
--
-- Okay, if the asymmetry is repeatedly causing problems, what about
-- dispensing with listy contexts entirely and using the categorical
-- concepts directly as the syntax?  Then there's no need to list out
-- every element of the context when defining `id`.
--
-- Nov 23:
--
-- One potentially-viable option here is to paper over the specific
-- issue of `f △ id` by adding that to the Cartesian category record,
-- and defining it directly with `π`; that would save it from being
-- linear in the size of the context.
--
-- Ignoring that particular issue, how costly would the
-- thinning-merging work be when using a co-de-Bruijn style of
-- binding?  Seems like it'd be quadratic-ish, which is just inherent
-- in how the module is currently constructed: there's a quadratic
-- number of projection morphisms, so anything that churns through
-- them in only quadratic time is doing about as well as it possibly
-- can.
--
-- Would using the CT concepts as the context be better
-- performance-wise, and would it be amenable to codegen?  Can I blend
-- that together with co-de-Bruijn (and is there a benefit to that)?
-- That is, find a way to forcibly hoist projections to the top of a
-- morphism?  From a quick consideration, this seems like it'd be
-- essentially the same (still a quadratic amount of structure being
-- described by Gel, still the same concepts used to simplify it, and
-- still passing in structures of names during codegen), but it'd lose
-- the familiarity of term languages / intuitionistic sequents.
--
-- Can I tweak the Gel library to let it prune the context more
-- aggressively somehow?  Tentative answer: this is probably worth
-- looking into, but I want to see some plausible-looking term
-- representations of circuits sooner rather than later, so try the
-- co-de-Bruijn thing.

-- Trial impl. of `_△_` with the existing logic: 
pairing
  : ∀ {Γ Δ Φ}
  → (∀ {A} → Module Δ A → Module Γ A)
  → (∀ {A} → Module Φ A → Module Γ A)
  → ∀ {A}
  → Module ((Δ ++ Φ) ++ Γ) A
  → Module Γ A
pairing {Δ = Δ} {Φ} f g m = record
  { body = {!!}
  {-
      π (g id .body)
        (π (weaken (Any.++⁺ʳ Φ) (f id .body))
        -- Hmm, the above two `id`s could be fairly expensive, in the
        -- case of `g ∘ (f △ id)`; how did we end up here again?  Is
        -- it required to be this way?  What about `Module (Δ ++ Γ) A
        -- → Module Γ A` as the core morphism type?
        --
        -- The core of the problem here is that even though the logic
        -- bakes in the idea that bindings are not implicitly dropped,
        -- the CT still bends over backwards to select and preserve
        -- all the intermediates, which leads to lots of modules that
        -- just build large tuples of their entire context.  So, the
        -- goal is either to make those benign, or to expose something
        -- further to the CT side of things to avoid constructing them
        -- in the first place.
          (weaken (λ B∈Δ++Φ → case Any.++⁻ Δ B∈Δ++Φ of λ
            { (inj₁ B∈Δ) → Any.++⁺ˡ B∈Δ
            ; (inj₂ B∈Φ) → Any.++⁺ʳ Δ (Any.++⁺ˡ B∈Φ)
            }) (m .body)))
            -}
  }

copairing
  : ∀ {Γ Δ Φ}
  → (∀ {A} → Module Γ A → Module Δ A)
  → (∀ {A} → Module Γ A → Module Φ A)
  → ∀ {A}
  → Module Γ A
  → Module (Δ ∐ Φ) A
copairing f g m = record
  { body = either var₀
      (π var₀ (weaken Any.++⁺ˡ (f m .body)))
      (π var₀ (weaken Any.++⁺ˡ (g m .body)))
  }
-}
