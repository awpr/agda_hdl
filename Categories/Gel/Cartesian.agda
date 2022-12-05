-- Notation for building cartesian category morphisms in terms of
-- functions on generalized elements: building a generalized element
-- of a product corresponds to building a morphism targeting a
-- product, etc.

open import Categories.Cartesian using (CartesianCategory)

module Categories.Gel.Cartesian {o m ℓ} (𝓒 : CartesianCategory o m ℓ) where

module 𝓒 = CartesianCategory 𝓒
open 𝓒 hiding (_⇒_)

open import Function using (it)
open import Level using (Level; _⊔_)

-- TODO: perhaps we can have a top-level transitivity instance instead
-- of doing QuantifiedConstraints everywhere?

record _⊇_ (X Y : Obj) : Set m where
  constructor MkSup
  field
    extract : X 𝓒.⇒ Y

open _⊇_

instance
  idInstance : ∀ {A} → A ⊇ A
  idInstance = MkSup id

  εInstance : ∀ {A} → A ⊇ ⋆
  εInstance = MkSup ε

-- Just a contravariant functor from `C` to, `Types`; what we care
-- about is its role as a presheaf, so that's what the record/class is
-- named.
record Presheaf {f} (F : 𝓒.Obj → Set f) : Set (o ⊔ m ⊔ f) where
  field
    contramap : ∀ {A B} → A 𝓒.⇒ B → F B → F A

open Presheaf ⦃ ... ⦄ public

-- TODO: something intermediate between Yoneda and Presheaf, that
-- involves a finite product of yoneda embeddings, or something like
-- that.

-- The Yoneda embedding of some object, wrapped in a record for
-- e.g. type inference reasons, or whatever other reason.
record Yoneda {f} (F : 𝓒.Obj → Set f) : Set (o ⊔ m ⊔ f) where
  field
    {O} : 𝓒.Obj
    wrap : ∀ {X} → X 𝓒.⇒ O → F X
    unwrap : ∀ {X} → F X → X 𝓒.⇒ O

  instance
    presheaf : Presheaf F
    presheaf = record { contramap = λ f x → wrap (unwrap x ∘ f) }

open Yoneda ⦃ ... ⦄ public using (wrap; unwrap)

private
  variable
    a b : Level
    A : Obj → Set a
    B : Obj → Set b

Rep : ∀ (A : Obj → Set a) → ⦃ Yoneda A ⦄ → Obj
Rep _ ⦃ yA ⦄ = Yoneda.O yA

-- Yoneda embedding.
⟦_⟧ : (A X : 𝓒.Obj) → Set m
⟦ A ⟧ X = X 𝓒.⇒ A

instance
  yonedaPresheaf : ∀ {A} → Presheaf ⟦ A ⟧
  yonedaPresheaf = record { contramap = Function.flip _∘_ }

  yonedaYoneda : ∀ {A} → Yoneda ⟦ A ⟧
  yonedaYoneda = record { wrap = Function.id ; unwrap = Function.id }

-- In the combined context of a [possibly closed-monoidal] category
-- and its presheaf category, there are a _ton_ of subtly different
-- notions of "arrows".  Let's just catalog a few here to help keep
-- things straight:
--
-- Without an "environment" or "enclosing scope":
--
-- * Normal morphisms of the category, `A 𝓒.⇒ B`
-- * Presheaf morphisms, `A ⟶ B` = `∀ {X} → A X → B X`
--   * This has a "scope" `X`, but as it's universally quantified,
--     it's "inaccessible" in this form.
--
-- With an "environment" or "enclosing scope":
--
-- * Monomorphic functions between presheaves, `(A ⇨ B) X` = `A X → B X`
--   * A pseudo-presheaf-exponential that appears when currying
--     "n-ary" presheaf morphisms à la **Set**:
--     `A ⊗ B ⟶ C` = `∀ {X} → A X × B X → C X` ⇔
--     `A ⟶ B ⇨ C` = `∀ {X} → A X → B X → C X`
--   * Since `X` is not quantified in `(A ⇨ B) X`, these can
--     incorporate other morphisms out of `X`.
--
-- * Yoneda embedding of exponentials, `⟦ A ↝ B ⟧ X` = `X 𝓒.⇒ A ↝ B`
--
-- * Uncurried form of the above, `(A ↣ B) X` = `A 𝓒.× X 𝓒.⇒ B`
--   * Used in certain [TODO] cases as an argument to a "higher order
--     morphism" where it should have access to the scope `X`.
--   * Can be produced by `Λ x ⇒ e` [TODO]
--
-- * Traditional presheaf exponentials, `⟦ X ⟧ ⊗ A ⟶ B` = `∀ {Y} → ⟦ X ⟧ Y × A Y → B Y`
--   * Not currently used.
--
-- * Curried, classy presheaf exponentials, `A ⇉ B` = `∀ {Y} → ⦃ Y ⊇₁ X ⦄ → A ∈ Y → B Y`
--   * Used by "variable binder" combinators like lambda, let-in.

-- For "multi-argument" presheaf morphisms, we'll present them in
-- curried form, and use the same naming convention as Setoids'
-- equality-preserving functions: _⟶_ introduces the "extra structure"
-- of quantification over `X`, and _⇨_ propagates it, so signatures look
-- like `A → B ⇨ C ⇨ D`.
infixr 20 _⟶_ _⇨_

-- ⇨ is \r7
_⇨_ : (A : 𝓒.Obj → Set a) → (B : 𝓒.Obj → Set b) → 𝓒.Obj → Set (a ⊔ b)
(A ⇨ B) X = A X → B X

-- ⟶ is \r--
_⟶_ : (A : 𝓒.Obj → Set a) → (B : 𝓒.Obj → Set b) → Set (o ⊔ a ⊔ b)
A ⟶ B = ∀ {X} → A X → B X

-- The type of locally-bound variables: `A ∈ X` is a morphism
-- projecting a "variable" of type `A` out of any scope lexically
-- contained within the scope `X`.
--
-- This is a whole lot like `X ⇒ A`, but leaning on Agda's instance
-- resolution algorithm to invisibly transport variables captured from
-- outer scopes into inner scopes.
--
-- Each binder provides its bound variable in the form of `A ∈ X` for
-- some scope `X`.  This can be used directly in scope `X` (by solving
-- `idInstance`), or in nested scopes by a chain of `_⊇_` instances
-- for each nesting.
_∈_ : (Obj → Set a) → Obj → Set (o ⊔ m ⊔ a)
A ∈ X = ∀ {Y} → ⦃ Y ⊇ X ⦄ → A Y

-- The type of scope nesting: `X ⊇ Y` is a constraint that the
-- bindings of scope `X` are a superset of those in the scope `Y`,
-- i.e. that `X` is nested inside `Y`.
--
-- This is a whole lot like `⟦ Y ⟧ X`, but again leaning on instance
-- resolution.
--
-- This is α-equivalent to `Y ∈ X`, but is used differently, as an
-- instance parameter.  Each binder provides an instance of this to
-- allow lifting variables of outer scope into the inner augmented
-- scope.
_⊇₁_ : Obj → Obj → Set (o ⊔ m)
X ⊇₁ Y = ∀ {Z} → ⦃ Z ⊇ X ⦄ → Z ⊇ Y

-- The type of "body" arguments to variable binders.  `A ⟨ X ⟩⇒ B` is
-- a function from a variable of type `A` to a generalized element of
-- type `B`, in scope `X`.
--
-- The actual scope is universally quantified so that instance
-- resolution can't mix up different scopes: the only scope-nesting
-- instance that can match the quantified scope is the one passed in
-- by the binder.
_⟨_⟩⇒_ : Obj → Obj → Obj → Set (o ⊔ m)
A ⟨ X ⟩⇒ B = ∀ {Y} → ⦃ Y ⊇₁ X ⦄ → ⟦ A ⟧ ∈ Y → ⟦ B ⟧ Y

_⇉_ : (Obj → Set a) → (Obj → Set b) → Obj → Set (o ⊔ m ⊔ a ⊔ b)
(A ⇉ B) X = ∀ {Y} → ⦃ Y ⊇₁ X ⦄ → A ∈ Y → B Y

-- The type of "body" arguments in the empty context.
--
-- Using a specialization of _⟨_⟩⇒_ tends to get in the way of
-- instance resolution, so instead of choosing X = ⋆ and expecting the
-- scope inclusion to be trivially solvable, we just omit the
-- constraint entirely.
_⋆⇒_ : (Obj → Set a) → (Obj → Set a) → Set (o ⊔ m ⊔ a)
A ⋆⇒ B = ∀ {Y} → A ∈ Y → B Y

infix 30 _↣_ -- Greater than _⟶_ and _⇨_, less than _×_

record _↣_
    (A : Obj → Set a)
    (B : Obj → Set b)
    ⦃ _ : Yoneda A ⦄
    (X : Obj)
    : Set b
    where
  constructor wrap↣
  field
    unwrap : B (Rep A × X)

instance
  presheaf↣ : ⦃ _ : Yoneda A ⦄ → ⦃ Presheaf B ⦄ → Presheaf (A ↣ B)
  presheaf↣ = record
    { contramap = λ f x → wrap↣ (contramap (p₁ △ f ∘ p₂) (_↣_.unwrap x))
    }

-- Turn the above "body" argument into a concrete morphism from the
-- scope and variable to the target.
--
-- This adapts the "convenient-to-write" form into the actual
-- underlying morphism, by supplying `p₁` as the scope nesting and
-- `p₂` as the variable projection.
reify
  : ∀ ⦃ _ : Yoneda A ⦄
  → (A ⇉ B) ⟶ A ↣ B
reify f = wrap↣ (f ⦃ MkSup (p₂ ∘ extract it) ⦄ (wrap (p₁ ∘ extract it)))

-- A variant used to avoid needless uses of `swap` when the "scope"
-- needs to be on the left for whatever reason.
reifyˡ : ∀ {X A B} → A ⟨ X ⟩⇒ B → X × A 𝓒.⇒ B
reifyˡ f = f ⦃ MkSup (p₁ ∘ extract it) ⦄ (p₂ ∘ extract it)

reify′ : ∀ ⦃ _ : Yoneda A ⦄ ⦃ _ : Yoneda B ⦄ → A ⋆⇒ B → Rep A 𝓒.⇒ Rep B
reify′ f = unwrap (f (wrap (extract it)))

infixr -2 reify′
syntax reify′ (λ x → e) = Λ x ⇒ e

-- Local subexpression binding: augment the scope with the given
-- generalized element, and continue in a nested scope.
--
-- This effectively implements sharing of "values" in morphisms: where
-- `let v = x in e[v]` would potentially duplicate the morphism `x`
-- many times and thus "compute" it independently many times,
-- `let-in x (λ v → e[v])` instead includes the morphism `x` once and
-- refers to its "result" by the bound variable `v` many times.
--
-- This can also be viewed as a generalization of composition where
-- the downstream morphism can still access the input of the upstream
-- morphism.
let-in
  : ⦃ _ : Yoneda A ⦄ ⦃ _ : Yoneda B ⦄
  → A ⟶ (A ⇉ B) ⇨ B
let-in x e = wrap (unwrap (_↣_.unwrap (reify e)) ∘ (unwrap x △ id))

module DoNotation where
  _>>=_
    : ⦃ _ : Yoneda A ⦄ ⦃ _ : Yoneda B ⦄
    → A ⟶ (A ⇉ B) ⇨ B
  _>>=_ = let-in

  -- Not sure if this will actually get any use since it can just as
  -- well be omitted, but by analogy to monadic do-notation, one can
  -- `return` a variable bound by a statement and/or >>=.
  return : A ⋆⇒ A
  return x = x

-- The product projections on generalized elements.
--
-- Internally, these just lift the projection morphisms to work on
-- generalized elements by composing them.
proj₁ : ∀ {A B} → ⟦ A × B ⟧ ⟶ ⟦ A ⟧
proj₁ x = p₁ ∘ x

proj₂ : ∀ {A B} → ⟦ A × B ⟧ ⟶ ⟦ B ⟧
proj₂ x = p₂ ∘ x

-- Application of morphisms to generalized elements.
--
-- Internally, this is just composition.
infixr -1 _$_ _$′_
_$_ : ∀ {A B} → A 𝓒.⇒ B → ⟦ A ⟧ ⟶ ⟦ B ⟧
f $ x = f ∘ x

_$′_ : ⦃ _ : Yoneda A ⦄ → ⦃ Presheaf B ⦄ → (A ↣ B) ⟶ A ⇨ B
f $′ x = contramap (unwrap x △ id) (_↣_.unwrap f)

-- Generalize a term to work in more-nested scopes.
--
-- Use this when creating a let-binding that you want to use after a
-- subsequent variable binding (in do-notation) / within a nested
-- scope (when using the combinators directly).
--
-- This can also be used to embed global elements `𝟏 ⇒ A` into any
-- scope, due to `εInstance`.
infix -2 !_
!_ : ∀ {a} {A : Obj → Set a} {X} ⦃ _ : Presheaf A ⦄ → A X → ∀ {Y} → ⦃ Y ⊇ X ⦄ → A Y
!_ x = contramap (extract it) x

-- Note for Monday Nov 7: currently thinking through what a logic
-- would look like where contexts are labeled by strings, conjunctions
-- are actually "records", i.e. contexts bundled up into a single
-- type, perhaps disjunctions are "named variants", and so on.  The
-- point of this is to turn it into a syntactic category, and use that
-- as a natural means to emit Verilog code: then spitting out
-- "morphisms" simply means emitting expressions with variable names
-- at the leaves, and the relevant categorical structures suffer only
-- negligibly from having to adapt between contexts and products.
-- Open questions:

-- * can this idea be further adapted to have a let-in construct in a
-- sensible way, so we can preserve sharing rather than exploding
-- duplicate circuitry like a traditional syntactic category would?
--
-- * would the result end up doing desirable normalization to get
-- sensible results out of the Categories.Gel `let-in`?
--
-- * will Agda be unhappy with us for trying to use string-keyed maps
-- and/or is a string-keyed approach worse than a labeled-vector
-- approach?

-- Nov 7 continuation: in fact, do variables even need to be
-- _identified_ by string names? can't we get the same properties by
-- making products be n-ary and contexts be vectors (i.e. using typed
-- de Bruijn indices)?  Then string names are merely user-supplied
-- annotations that give hints about what names should be used by
-- generated code, upstream and downstream.
--
-- Observation: the shift from singular objects to contexts (or,
-- rather, the choice of framing the syntactic category in terms of
-- contexts rather than in terms of single usually-product types) is
-- exactly a strategy for adapting between the projections of CT and
-- the variable references of traditional type theories.  That
-- syntactic categories' morphisms _target_ contexts too is simply a
-- result of CT being "symmetrical", in that sources and targets must
-- be drawn from the same set of objects.
--
-- The core conflict I'm wrestling with is this: the traditional
-- presentation of a type theory / logic is built around single terms
-- (with product introduction rules).  That presentation is amenable
-- to a let-in construct, e.g. as seen in Haskell Core.  But if the CT
-- adaptation wants to be able to produce entire substitutions, a
-- let-in term former is no longer sufficient, because it doesn't
-- permit sharing between distinct elements of the resulting context;
-- a let-in would need to scope its bindings over _multiple_ terms.
-- So, the question becomes: what should the logic look like to
-- accommodate this type of sharing, and is the difference made in the
-- core of the logic itself or in the data type used to represent the
-- morphisms?  That is, do I need to change the very nature of the
-- logic, or do I still define a traditional type theory for the terms
-- and then make only the type of morphisms nontraditional?
--
-- Nov 8 note: the symmetry of both sources and targets being contexts
-- is better aligned with linear logic, where sequents have contexts
-- on both sides, and those contexts are seen as implicitly connected
-- by dual connectives according to which side they're on.  Can this
-- be exploited to yield a better adaptation between CT and Verilog
-- than a more traditional term-oriented type theory wrapped into
-- substitutions?
