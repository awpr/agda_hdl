-- Notation for building cartesian category morphisms in terms of
-- functions on generalized elements: building a generalized element
-- of a product corresponds to building a morphism targeting a
-- product, etc.

open import Categories.Cartesian using (CartesianCategory)

module Categories.Gel.Cartesian {o m β} (π : CartesianCategory o m β) where

module π = CartesianCategory π
open π hiding (_β_)

open import Function using (it)
open import Level using (Level; _β_)

-- TODO: perhaps we can have a top-level transitivity instance instead
-- of doing QuantifiedConstraints everywhere?

record _β_ (X Y : Obj) : Set m where
  constructor MkSup
  field
    extract : X π.β Y

open _β_

instance
  idInstance : β {A} β A β A
  idInstance = MkSup id

  Ξ΅Instance : β {A} β A β β
  Ξ΅Instance = MkSup Ξ΅

-- Just a contravariant functor from `C` to, `Types`; what we care
-- about is its role as a presheaf, so that's what the record/class is
-- named.
record Presheaf {f} (F : π.Obj β Set f) : Set (o β m β f) where
  field
    contramap : β {A B} β A π.β B β F B β F A

open Presheaf β¦ ... β¦ public

-- TODO: something intermediate between Yoneda and Presheaf, that
-- involves a finite product of yoneda embeddings, or something like
-- that.

-- The Yoneda embedding of some object, wrapped in a record for
-- e.g. type inference reasons, or whatever other reason.
record Yoneda {f} (F : π.Obj β Set f) : Set (o β m β f) where
  field
    {O} : π.Obj
    wrap : β {X} β X π.β O β F X
    unwrap : β {X} β F X β X π.β O

  instance
    presheaf : Presheaf F
    presheaf = record { contramap = Ξ» f x β wrap (unwrap x β f) }

open Yoneda β¦ ... β¦ public using (wrap; unwrap)

private
  variable
    a b : Level
    A : Obj β Set a
    B : Obj β Set b

Rep : β (A : Obj β Set a) β β¦ Yoneda A β¦ β Obj
Rep _ β¦ yA β¦ = Yoneda.O yA

-- Yoneda embedding.
β¦_β§ : (A X : π.Obj) β Set m
β¦ A β§ X = X π.β A

instance
  yonedaPresheaf : β {A} β Presheaf β¦ A β§
  yonedaPresheaf = record { contramap = Function.flip _β_ }

  yonedaYoneda : β {A} β Yoneda β¦ A β§
  yonedaYoneda = record { wrap = Function.id ; unwrap = Function.id }

-- In the combined context of a [possibly closed-monoidal] category
-- and its presheaf category, there are a _ton_ of subtly different
-- notions of "arrows".  Let's just catalog a few here to help keep
-- things straight:
--
-- Without an "environment" or "enclosing scope":
--
-- * Normal morphisms of the category, `A π.β B`
-- * Presheaf morphisms, `A βΆ B` = `β {X} β A X β B X`
--   * This has a "scope" `X`, but as it's universally quantified,
--     it's "inaccessible" in this form.
--
-- With an "environment" or "enclosing scope":
--
-- * Monomorphic functions between presheaves, `(A β¨ B) X` = `A X β B X`
--   * A pseudo-presheaf-exponential that appears when currying
--     "n-ary" presheaf morphisms Γ  la **Set**:
--     `A β B βΆ C` = `β {X} β A X Γ B X β C X` β
--     `A βΆ B β¨ C` = `β {X} β A X β B X β C X`
--   * Since `X` is not quantified in `(A β¨ B) X`, these can
--     incorporate other morphisms out of `X`.
--
-- * Yoneda embedding of exponentials, `β¦ A β B β§ X` = `X π.β A β B`
--
-- * Uncurried form of the above, `(A β£ B) X` = `A π.Γ X π.β B`
--   * Used in certain [TODO] cases as an argument to a "higher order
--     morphism" where it should have access to the scope `X`.
--   * Can be produced by `Ξ x β e` [TODO]
--
-- * Traditional presheaf exponentials, `β¦ X β§ β A βΆ B` = `β {Y} β β¦ X β§ Y Γ A Y β B Y`
--   * Not currently used.
--
-- * Curried, classy presheaf exponentials, `A β B` = `β {Y} β β¦ Y ββ X β¦ β A β Y β B Y`
--   * Used by "variable binder" combinators like lambda, let-in.

-- For "multi-argument" presheaf morphisms, we'll present them in
-- curried form, and use the same naming convention as Setoids'
-- equality-preserving functions: _βΆ_ introduces the "extra structure"
-- of quantification over `X`, and _β¨_ propagates it, so signatures look
-- like `A β B β¨ C β¨ D`.
infixr 20 _βΆ_ _β¨_

-- β¨ is \r7
_β¨_ : (A : π.Obj β Set a) β (B : π.Obj β Set b) β π.Obj β Set (a β b)
(A β¨ B) X = A X β B X

-- βΆ is \r--
_βΆ_ : (A : π.Obj β Set a) β (B : π.Obj β Set b) β Set (o β a β b)
A βΆ B = β {X} β A X β B X

-- The type of locally-bound variables: `A β X` is a morphism
-- projecting a "variable" of type `A` out of any scope lexically
-- contained within the scope `X`.
--
-- This is a whole lot like `X β A`, but leaning on Agda's instance
-- resolution algorithm to invisibly transport variables captured from
-- outer scopes into inner scopes.
--
-- Each binder provides its bound variable in the form of `A β X` for
-- some scope `X`.  This can be used directly in scope `X` (by solving
-- `idInstance`), or in nested scopes by a chain of `_β_` instances
-- for each nesting.
_β_ : (Obj β Set a) β Obj β Set (o β m β a)
A β X = β {Y} β β¦ Y β X β¦ β A Y

-- The type of scope nesting: `X β Y` is a constraint that the
-- bindings of scope `X` are a superset of those in the scope `Y`,
-- i.e. that `X` is nested inside `Y`.
--
-- This is a whole lot like `β¦ Y β§ X`, but again leaning on instance
-- resolution.
--
-- This is Ξ±-equivalent to `Y β X`, but is used differently, as an
-- instance parameter.  Each binder provides an instance of this to
-- allow lifting variables of outer scope into the inner augmented
-- scope.
_ββ_ : Obj β Obj β Set (o β m)
X ββ Y = β {Z} β β¦ Z β X β¦ β Z β Y

-- The type of "body" arguments to variable binders.  `A β¨ X β©β B` is
-- a function from a variable of type `A` to a generalized element of
-- type `B`, in scope `X`.
--
-- The actual scope is universally quantified so that instance
-- resolution can't mix up different scopes: the only scope-nesting
-- instance that can match the quantified scope is the one passed in
-- by the binder.
_β¨_β©β_ : Obj β Obj β Obj β Set (o β m)
A β¨ X β©β B = β {Y} β β¦ Y ββ X β¦ β β¦ A β§ β Y β β¦ B β§ Y

_β_ : (Obj β Set a) β (Obj β Set b) β Obj β Set (o β m β a β b)
(A β B) X = β {Y} β β¦ Y ββ X β¦ β A β Y β B Y

-- The type of "body" arguments in the empty context.
--
-- Using a specialization of _β¨_β©β_ tends to get in the way of
-- instance resolution, so instead of choosing X = β and expecting the
-- scope inclusion to be trivially solvable, we just omit the
-- constraint entirely.
_ββ_ : (Obj β Set a) β (Obj β Set a) β Set (o β m β a)
A ββ B = β {Y} β A β Y β B Y

infix 30 _β£_ -- Greater than _βΆ_ and _β¨_, less than _Γ_

record _β£_
    (A : Obj β Set a)
    (B : Obj β Set b)
    β¦ _ : Yoneda A β¦
    (X : Obj)
    : Set b
    where
  constructor wrapβ£
  field
    unwrap : B (Rep A Γ X)

instance
  presheafβ£ : β¦ _ : Yoneda A β¦ β β¦ Presheaf B β¦ β Presheaf (A β£ B)
  presheafβ£ = record
    { contramap = Ξ» f x β wrapβ£ (contramap (pβ β³ f β pβ) (_β£_.unwrap x))
    }

-- Turn the above "body" argument into a concrete morphism from the
-- scope and variable to the target.
--
-- This adapts the "convenient-to-write" form into the actual
-- underlying morphism, by supplying `pβ` as the scope nesting and
-- `pβ` as the variable projection.
reify
  : β β¦ _ : Yoneda A β¦
  β (A β B) βΆ A β£ B
reify f = wrapβ£ (f β¦ MkSup (pβ β extract it) β¦ (wrap (pβ β extract it)))

-- A variant used to avoid needless uses of `swap` when the "scope"
-- needs to be on the left for whatever reason.
reifyΛ‘ : β {X A B} β A β¨ X β©β B β X Γ A π.β B
reifyΛ‘ f = f β¦ MkSup (pβ β extract it) β¦ (pβ β extract it)

reifyβ² : β β¦ _ : Yoneda A β¦ β¦ _ : Yoneda B β¦ β A ββ B β Rep A π.β Rep B
reifyβ² f = unwrap (f (wrap (extract it)))

infixr -2 reifyβ²
syntax reifyβ² (Ξ» x β e) = Ξ x β e

-- Local subexpression binding: augment the scope with the given
-- generalized element, and continue in a nested scope.
--
-- This effectively implements sharing of "values" in morphisms: where
-- `let v = x in e[v]` would potentially duplicate the morphism `x`
-- many times and thus "compute" it independently many times,
-- `let-in x (Ξ» v β e[v])` instead includes the morphism `x` once and
-- refers to its "result" by the bound variable `v` many times.
--
-- This can also be viewed as a generalization of composition where
-- the downstream morphism can still access the input of the upstream
-- morphism.
let-in
  : β¦ _ : Yoneda A β¦ β¦ _ : Yoneda B β¦
  β A βΆ (A β B) β¨ B
let-in x e = wrap (unwrap (_β£_.unwrap (reify e)) β (unwrap x β³ id))

module DoNotation where
  _>>=_
    : β¦ _ : Yoneda A β¦ β¦ _ : Yoneda B β¦
    β A βΆ (A β B) β¨ B
  _>>=_ = let-in

  -- Not sure if this will actually get any use since it can just as
  -- well be omitted, but by analogy to monadic do-notation, one can
  -- `return` a variable bound by a statement and/or >>=.
  return : A ββ A
  return x = x

-- The product projections on generalized elements.
--
-- Internally, these just lift the projection morphisms to work on
-- generalized elements by composing them.
projβ : β {A B} β β¦ A Γ B β§ βΆ β¦ A β§
projβ x = pβ β x

projβ : β {A B} β β¦ A Γ B β§ βΆ β¦ B β§
projβ x = pβ β x

-- Application of morphisms to generalized elements.
--
-- Internally, this is just composition.
infixr -1 _$_ _$β²_
_$_ : β {A B} β A π.β B β β¦ A β§ βΆ β¦ B β§
f $ x = f β x

_$β²_ : β¦ _ : Yoneda A β¦ β β¦ Presheaf B β¦ β (A β£ B) βΆ A β¨ B
f $β² x = contramap (unwrap x β³ id) (_β£_.unwrap f)

-- Generalize a term to work in more-nested scopes.
--
-- Use this when creating a let-binding that you want to use after a
-- subsequent variable binding (in do-notation) / within a nested
-- scope (when using the combinators directly).
--
-- This can also be used to embed global elements `π β A` into any
-- scope, due to `Ξ΅Instance`.
infix -2 !_
!_ : β {a} {A : Obj β Set a} {X} β¦ _ : Presheaf A β¦ β A X β β {Y} β β¦ Y β X β¦ β A Y
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
