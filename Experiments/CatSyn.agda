{-# OPTIONS --safe #-}

module Experiments.CatSyn where

open import Agda.Builtin.Reflection using (withReconstructed)
open import Agda.Primitive using (Setω)

open import Category.Monad using (RawMonad)
import Category.Monad.Reader as Reader
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin)
open import Data.List as List using (List; _∷_; [])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe as Maybe using (Maybe; just; nothing; maybe; fromMaybe; _<∣>_)
open import Data.Nat as ℕ using (ℕ; suc; zero)
import Data.Nat.Show as ℕ
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.String as String using (String)
open import Data.Unit using (⊤; tt)
open import Function using (_$_; it; case_of_)
open import Level using (Level; _⊔_)
open import Reflection.DeBruijn using (η-expand; weaken; strengthenBy)
open import Reflection.Term
open import Reflection.Abstraction
open import Reflection.Argument
open import Reflection.Argument.Visibility
open import Reflection.Show
open import Reflection.TypeChecking.Monad hiding (return)
import Reflection.TypeChecking.Monad.Categorical as TCM
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Categories

{- An attempt at a better-inferring way to write type signatures for morphisms

data ObjSyn {o m} (cat : Cat o m) : Set (o ⊔ m) where
  ⟨_⟩ : Cat.Obj cat → ObjSyn cat

  _:⊗_ : ⦃ RawMonoidal (Cat.Obj cat) (Cat.Mor cat) ⦄ → (A B : ObjSyn cat) → ObjSyn cat
  :⊤ : ⦃ RawTerminal (Cat.Obj cat) (Cat.Mor cat) ⦄ → ObjSyn cat

  _:↝_ : ⦃ RawCartesianClosed (Cat.Obj cat) (Cat.Mor cat) ⦄ → (A B : ObjSyn cat) → ObjSyn cat

interpAsObj : ∀ {o m} {cat : Cat o m} → ObjSyn cat → Cat.Obj cat
interpAsObj ⟨ x ⟩ = x
interpAsObj (a :⊗ b) = interpAsObj a ⊗ interpAsObj b
interpAsObj :⊤ = ⋆
interpAsObj (a :↝ b) = interpAsObj a ↝ interpAsObj b

interpAsType : ∀ {o m} {cat : Cat o m} → ObjSyn cat → Set
interpAsType {cat = cat} ⟨ x ⟩ = cat ⟦ x ⟧
interpAsType (a :⊗ b) = interpAsType a × interpAsType b
interpAsType :⊤ = ⊤
interpAsType (a :↝ b) = interpAsType a → interpAsType b

record [_]_:⇒_ {o m} (cat : Cat o m) (A B : ObjSyn cat) : Set m where
  field
    morphism : Cat.Mor cat (interpAsObj A) (interpAsObj B)

thing : ∀ {o m} {cat : Cat o m} {A B : ObjSyn cat} → (interpAsType A → interpAsType B) → [ cat ] A :⇒ B
thing = {!!}

example : ∀ {o m} {cat : Cat o m} ⦃ _ : RawMonoidal (Cat.Obj cat) (Cat.Mor cat) ⦄ {A B C} → [ cat ] (⟨ A ⟩ :⊗ (⟨ B ⟩ :⊗ ⟨ C ⟩)) :⇒ ⟨ C ⟩
example = thing λ x → {!!}
-}

module CategorySyntax {o m ℓ} (C : Category o m ℓ) where
  open Category C

  data ⟦_⟧ (A : Obj) : Set where
    opaque : ⟦ A ⟧

  infixr 40 _⟨$⟩_
  _⟨$⟩_ : {A B : Obj} → A ⇒ B → ⟦ A ⟧ → ⟦ B ⟧
  f ⟨$⟩ opaque = opaque


module MonoidalSyntax {o m ℓ} {C : Category o m ℓ} (mon : Monoidal C) where
  open Category C
  open Monoidal mon
  open CategorySyntax C public

  unpack⊗
    : {A B : Obj}
    → ⟦ A ⊗ B ⟧ → ⟦ A ⟧ × ⟦ B ⟧
  unpack⊗ opaque = opaque , opaque

  pack⊗
    : {A B : Obj}
    → ⟦ A ⟧ × ⟦ B ⟧ → ⟦ A ⊗ B ⟧
  pack⊗ (x , y) = opaque

  `tt : ⟦ 𝟏 ⟧
  `tt = opaque

  infixr 60 _`,_
  _`,_
    : {A B : Obj}
    → ⟦ A ⟧ → ⟦ B ⟧ → ⟦ A ⊗ B ⟧
  opaque `, opaque = opaque

module CartesianSyntax {o m ℓ} {C : Category o m ℓ} (cart : Cartesian C) where
  open Category C
  open MonoidalSyntax (Cartesian.monoidal cart) public

  let-in
    : ∀ {a} {A : Set a} {B : Obj}
    → (A → ⟦ B ⟧) → A → ⟦ B ⟧
  let-in b x = opaque

  syntax let-in (λ x → e) e₂ = ⟨ x ≔ e₂ ⟩ e

module ClosedSyntax {o m ℓ} {C : Category o m ℓ} (closed : CartesianClosed C) where
  open Category C
  open CartesianClosed closed
  open CartesianSyntax cartesian public

  pack↝
    : {A B : Obj}
    → (⟦ A ⟧ → ⟦ B ⟧) → ⟦ A ↝ B ⟧
  pack↝ f = opaque

  syntax pack↝ (λ x → e) = Λ x ↝ e

  infixr 20 _`$_
  _`$_
    : {A B : Obj}
    → ⟦ A ↝ B ⟧ → ⟦ A ⟧ → ⟦ B ⟧
  opaque `$ opaque = opaque

record CategoryTranslation : Set where
  field
    `id : Term
    `compose : Term → Term → Term

open CategoryTranslation

record TerminalTranslation : Set where
  field
    `ε : Term

open TerminalTranslation

record MonoidalTranslation : Set where
  field
    `bimap⊗ : Term → Term → Term
    `first⊗ : Term → Term
    `second⊗ : Term → Term

open MonoidalTranslation

record CartesianTranslation : Set where
  field
    `proj₁ : Term
    `proj₂ : Term
    `δ : Term
    `Δ : Term → Term → Term

open CartesianTranslation

record CartesianClosedTranslation : Set where
  field
    `curry : Term → Term
    `uncurry : Term → Term
    `apply : Term → Term → Term

open CartesianClosedTranslation

record Translation : Set where
  field
    category : Maybe CategoryTranslation
    monoidal : Maybe MonoidalTranslation
    terminal : Maybe TerminalTranslation
    cartesian : Maybe CartesianTranslation
    closed : Maybe CartesianClosedTranslation

module _ where
  open RawMonad (TCM.monad {Level.zero}) hiding (_⊗_)

  infixl 20 _$$_
  _$$_ : Term → Term → Term
  f $$ x = def (quote Function._$_) (f ⟨∷⟩ x ⟨∷⟩ [])

  tm1 : Term → Term → Term
  tm1 f x = f $$ x

  tm2 : Term → (Term → Term → Term)
  tm2 f x y = def (quote Function._⟨_⟩_) (x ⟨∷⟩ f ⟨∷⟩ y ⟨∷⟩ [])

  buildCategory : ∀ {o m ℓ} → Category o m ℓ → TC CategoryTranslation
  buildCategory C = do
    let open Category C
    `id ← quoteTC {A = ∀ {A} → A ⇒ A} (Category.id C)
    `compose ← quoteTC {A = ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C} (Category._∘_ C)
    return $ record { `id = `id; `compose = tm2 `compose }

  buildTerminal
    : ∀ {o m ℓ} {C : Category o m ℓ}
    → TerminalObject C → TC TerminalTranslation
  buildTerminal {C = C} term = do
    `ε ← quoteTC {A = ∀ {A} → A ⇒ (TerminalObject.⋆ term)} (TerminalObject.ε term)
    return $ record { `ε = `ε }
   where
    open Category C

  buildMonoidal
    : ∀ {o m ℓ} {C : Category o m ℓ}
    → Monoidal C → TC MonoidalTranslation
  buildMonoidal {C = C} mon = do
    `bimap ← quoteTC {A = ∀ {A B C D} → A ⇒ C → B ⇒ D → _} (Monoidal.bimap⊗ mon)
    `first ← quoteTC
      {A = ∀ {A B C} → A ⇒ B → A ⊗ C ⇒ _}
      first⊗
    `second ← quoteTC
      {A = ∀ {A B C} → A ⇒ B → C ⊗ A ⇒ _}
      second⊗
    return $ record
      { `bimap⊗ = tm2 `bimap
      ; `first⊗ = tm1 `first
      ; `second⊗ = tm1 `second
      }
   where
    open Category C
    open Monoidal mon

  buildCartesian
    : ∀ {o m ℓ} {C : Category o m ℓ}
    → Cartesian C → TC CartesianTranslation
  buildCartesian {C = C} cart = do
    `proj₁ ← quoteTC {A = ∀ {A B} → A ⊗ B ⇒ A} p₁
    `proj₂ ← quoteTC {A = ∀ {A B} → A ⊗ B ⇒ B} p₂
    `δ ← quoteTC {A = ∀ {A} → A ⇒ _} δ
    `Δ ← quoteTC {A = ∀ {A B C} → A ⇒ B → A ⇒ C → A ⇒ _} _△_
    return $ record
      { `proj₁ = `proj₁
      ; `proj₂ = `proj₂
      ; `δ = `δ
      ; `Δ = tm2 `Δ
      }
   where
    open Category C
    open Cartesian cart
    open Monoidal monoidal

  buildClosed
    : ∀ {o m ℓ} {C : Category o m ℓ}
    → CartesianClosed C → TC CartesianClosedTranslation
  buildClosed {C = C} closed = do
    `curry ← quoteTC {A = ∀ {A B C} → A ⊗ B ⇒ C → A ⇒ _} curryʳ
    `uncurry ← quoteTC {A = ∀ {A B C} → A ⇒ _ → A ⊗ B ⇒ C} uncurryʳ
    `apply ← quoteTC {A = ∀ {A B C} → C ⇒ _ → C ⇒ A → C ⇒ B} app
    return $ record { `curry = tm1 `curry ; `uncurry = tm1 `uncurry ; `apply = tm2 `apply }
   where
    open Category C
    open CartesianClosed closed
    open Monoidal monoidal

  buildCCC
    : ∀ {o m ℓ} {C : Category o m ℓ}
    → CartesianClosed C → TC Translation
  buildCCC {C = C} ccc = do
    let cart = CartesianClosed.cartesian ccc
        mon = Cartesian.monoidal cart
    cat′ ← buildCategory C
    mon′ ← buildMonoidal mon
    term′ ← buildTerminal (Cartesian.terminal cart)
    cart′ ← buildCartesian cart
    closed′ ← buildClosed ccc
    return $ record
      { category = just cat′
      ; monoidal = just mon′
      ; terminal = just term′
      ; cartesian = just cart′
      ; closed = just closed′
      }

  buildCC
    : ∀ {o m ℓ} {C : Category o m ℓ}
    → Cartesian C → TC Translation
  buildCC {C = C} cc = do
    let mon = Cartesian.monoidal cc
    cat′ ← buildCategory C
    mon′ ← buildMonoidal mon
    term′ ← buildTerminal (Cartesian.terminal cc)
    cart′ ← buildCartesian cc
    return $ record
      { category = just cat′
      ; monoidal = just mon′
      ; terminal = just term′
      ; cartesian = just cart′
      ; closed = nothing
      }

module _ {o m ℓ} (C : Category o m ℓ) where
  open Category C
  open CategorySyntax C

  data ObjDesc : Set (o ⊔ m ⊔ ℓ) where
    Opaque : Obj → ObjDesc
    Exp : ⦃ CartesianClosed C ⦄ → (A B : ObjDesc) → ObjDesc

    Prod : ⦃ Monoidal C ⦄ → (A B : ObjDesc) → ObjDesc
    Top : ⦃ TerminalObject C ⦄ → ObjDesc

    -- Sum : (A B : ObjDesc cat) → ObjDesc cat
    -- Bot : ObjDesc cat

  interp : ObjDesc → Set
  interp (Opaque x) = ⟦ x ⟧
  interp (Exp A B) = interp A → interp B
  interp (Prod A B) = interp A × interp B
  -- interp (Sum A B) = interp A ⊎ interp B
  interp Top = ⊤
  -- interp Bot = ⊥

  interpAsObj : ObjDesc → Obj
  interpAsObj (Opaque x) = x
  interpAsObj (Exp ⦃ closed ⦄ A B) = CartesianClosed._↝_ closed (interpAsObj A) (interpAsObj B)
  interpAsObj (Prod ⦃ mon ⦄ A B) = Monoidal._⊗_ mon (interpAsObj A) (interpAsObj B)
  interpAsObj (Top ⦃ term ⦄) = TerminalObject.⋆ term

guessTelescope : ℕ → Pattern → (ℕ × List (String × Arg Type))
guessTelescope n₀ (con c ps₀) = go n₀ ps₀
 where
  go : ℕ → List (Arg Pattern) → (ℕ × List (String × Arg Type))
  go n [] = n , []
  go n (arg _ p ∷ ps) =
    let (n′ , tel₀) = guessTelescope n p
        (n″ , tel₁) = go n′ ps
    in  (n″ , tel₀ List.++ tel₁)

guessTelescope n (dot t) = n , []
guessTelescope n (var x) = ℕ.suc n , ("x" String.++ ℕ.show n , vArg unknown) ∷ []
guessTelescope n (lit l) = n , []
guessTelescope n (proj f) = n , []
guessTelescope n (absurd x) = n , []

trimTerm : ℕ → Term → Term
trimArgs : ℕ → List (Arg Term) → List (Arg Term)
trimClause : ℕ → Clause → Clause
trimClauses : ℕ → List Clause → List Clause
trimPat : ℕ → Pattern → Pattern
trimPats : ℕ → List (Arg Pattern) → List (Arg Pattern)
trimTel : ℕ → List (String × Arg Type) → List (String × Arg Type)

trimTerm zero _ = unknown
trimTerm (suc n) (var x args) = var x (trimArgs n args)
trimTerm (suc n) (con c args) = con c (trimArgs n args)
trimTerm (suc n) (def f args) = def f (trimArgs n args)
trimTerm (suc n) (lam v (abs nm t)) = lam v (abs nm (trimTerm n t))
trimTerm (suc n) (pat-lam cs args) = pat-lam (trimClauses n cs) (trimArgs n args)
trimTerm (suc n) (pi (arg i a) (abs nm b)) = pi (arg i (trimTerm n a)) (abs nm (trimTerm n b))
trimTerm (suc n) (sort s) = sort s -- laziness
trimTerm (suc n) (lit l) = lit l
trimTerm (suc n) (meta x args) = meta x (trimArgs n args)
trimTerm (suc n) unknown = unknown

trimArgs n [] = []
trimArgs n (arg i x ∷ xs) = arg i (trimTerm n x) ∷ trimArgs n xs

trimClauses n [] = []
trimClauses n (x ∷ cs) = trimClause n x ∷ trimClauses n cs

trimClause n (clause tel ps t) = clause (trimTel n tel) (trimPats n ps) (trimTerm n t)
trimClause n (absurd-clause tel ps) = absurd-clause (trimTel n tel) (trimPats n ps)

trimPat zero _ = dot unknown
trimPat (suc n) (con c ps) = con c (trimPats n ps)
trimPat (suc n) (dot t) = dot (trimTerm n t)
trimPat (suc n) (var x) = var x
trimPat (suc n) (lit l) = lit l
trimPat (suc n) (proj f) = proj f
trimPat (suc n) (absurd x) = absurd x

trimPats n [] = []
trimPats n (arg i p ∷ ps) = arg i (trimPat n p) ∷ trimPats n ps

trimTel n [] = []
trimTel n ((nm , arg i t) ∷ tel) = (nm , arg i (trimTerm n t)) ∷ trimTel n tel

weakenPat : ℕ → Pattern → Pattern
weakenPat n (con c ps) = con c (go ps)
 where
  go : List (Arg Pattern) → List (Arg Pattern)
  go [] = []
  go (arg i x ∷ xs) = arg i (weakenPat n x) ∷ go xs
weakenPat n (dot t) = dot (weaken n t)
weakenPat n (var x) = var (n ℕ.+ x)
weakenPat n (lit l) = lit l
weakenPat n (proj f) = proj f
weakenPat n (absurd x) = absurd (n ℕ.+ x)

data IdTerm : Set where
  id : IdTerm
  term : Term → IdTerm

module _ where
  open Reader Translation Level.zero using (RawMonadReader; ReaderTMonadReader; ReaderT)
  open RawMonadReader (ReaderTMonadReader TCM.monad)

  GenM : ∀ (A : Set) → Set
  GenM = ReaderT TC

  lift : ∀ {A : Set} → TC A → GenM A
  lift x _ = x

  getCategory : GenM CategoryTranslation
  getCategory = do
    just x ← asks Translation.category
     where
      nothing → lift $ typeError (strErr "Missing CategoryTranslation" ∷ [])
    return x

  getCartesian : GenM CartesianTranslation
  getCartesian = do
    just x ← asks Translation.cartesian
     where
      nothing → lift $ typeError (strErr "Missing CartesianTranslation" ∷ [])
    return x

  getTerminal : GenM TerminalTranslation
  getTerminal = do
    just x ← asks Translation.terminal
     where
      nothing → lift $ typeError (strErr "Missing TerminalTranslation" ∷ [])
    return x

  getClosed : GenM CartesianClosedTranslation
  getClosed = do
    just x ← asks Translation.closed
     where
      nothing → lift $ typeError (strErr "Missing CartesianClosedTranslation" ∷ [])
    return x

  -- The projection morphism on its own.
  getProj₁ : GenM IdTerm
  getProj₁ = do
    c ← getCartesian
    return $ term $ `proj₁ c

  getProj₂ : GenM IdTerm
  getProj₂ = do
    c ← getCartesian
    return $ term $ `proj₂ c

  getε : GenM IdTerm
  getε = do
    c ← getTerminal
    return $ term $ `ε c

  mkCompose : IdTerm → IdTerm → GenM IdTerm
  mkCompose id g = return g
  mkCompose f id = return f
  mkCompose (term f) (term g) = do
    c ← getCategory
    return $ term $ `compose c f g

  -- The projection as an operation on "generalized elements"
  mkProj₁ : IdTerm → GenM IdTerm
  mkProj₁ t = do
    x ← getProj₁
    mkCompose x t

  mkProj₂ : IdTerm → GenM IdTerm
  mkProj₂ t = do
    x ← getProj₂
    mkCompose x t

  toTerm : IdTerm → GenM Term
  toTerm id = do
    c ← getCategory
    return $ `id c
  toTerm (term t) = return t

  mkCurry : IdTerm → GenM IdTerm
  mkCurry f = do
    c ← getClosed
    f′ ← toTerm f
    return $ term $ `curry c f′

  mkΔ : IdTerm → IdTerm → GenM IdTerm
  mkΔ id id = do
    c ← getCartesian
    return $ term $ `δ c
  mkΔ f g = do
    c ← getCartesian
    f′ ← toTerm f
    g′ ← toTerm g
    return $ term $ `Δ c f′ g′

  mkApp : IdTerm → IdTerm → GenM IdTerm
  mkApp f id = do
    clo ← getClosed
    cart ← getCartesian
    f′ ← toTerm f
    mkCompose (term $ `uncurry clo f′) (term $ `δ cart)
  mkApp f (term x) = do
    clo ← getClosed
    f′ ← toTerm f
    return $ term $ `apply clo f′ x

  findVar : Pattern → ℕ → GenM (Maybe IdTerm)
  findVar (con c (vArg l ∷ vArg r ∷ [])) n = do
    l′ ← findVar l n
    r′ ← findVar r n
    case (l′ , r′) of λ
      { (just l″ , _)       → just <$> mkProj₁ l″
      ; (nothing , just r″) → just <$> mkProj₂ r″
      ; (nothing , nothing) → return nothing
      }
  findVar (con c _) n =
    lift $ typeError (strErr "Unsupported non-binary product constructor." ∷ [])
  findVar (dot t) n = return nothing
  findVar (var x) n with x ℕ.≡ᵇ n
  ... | false = return nothing
  ... | true = return $ just id
  findVar (lit l) n = return nothing
  findVar (proj f) n = return nothing
  findVar (absurd x) n with x ℕ.≡ᵇ n
  ... | false = return nothing
  ... | true = return $ just id

  -- the ℕ is the number of lambda binders we've consumed: we're taking
  -- apart terms and eliminating binders, so we'll need to strengthen
  -- any preserved parts of the term according to how many binders we
  -- deleted around it.
  buildMorphism : ℕ → Pattern → Term → GenM IdTerm
  buildApplication : ℕ → Pattern → IdTerm → List (Arg Term) → GenM IdTerm

  buildApplication n pat f [] = return f
  buildApplication n pat f (arg i x ∷ xs) = do
    x′ ← buildMorphism n pat x
    fx ← mkApp f x′
    buildApplication n pat fx xs

  buildMorphism n pat tm@(def (quote CategorySyntax._⟨$⟩_) (o ∷ m ∷ C ∷ A ∷ B ∷ f ⟨∷⟩ x ⟨∷⟩ [])) =
    do
      x′ ← buildMorphism n pat x
      just f′ ← return $ strengthenBy n f
       where
        nothing → do
          f′ ← lift $ quoteTC f
          lift $ typeError $
            strErr "LHS of _⟨$⟩_ contains lambda-bound variables: " ∷ termErr f′ ∷ []
      mkCompose (term f′) x′

  buildMorphism n pat (con (quote _,_) (a ∷ b ∷ A ∷ B ∷ x ⟨∷⟩ y ⟨∷⟩ [])) =
    do
      x′ ← buildMorphism n pat x
      y′ ← buildMorphism n pat y
      mkΔ x′ y′

  buildMorphism n pat (def (quote MonoidalSyntax._`,_) (o ∷ m ∷ C ∷ mon ∷ A ∷ B ∷ args)) with args
  ... | x ⟨∷⟩ y ⟨∷⟩ [] =
    do
      x′ ← buildMorphism n pat x
      y′ ← buildMorphism n pat y
      mkΔ x′ y′
  ... | args =
    do
      pr₁ ← getProj₁
      pr₂ ← getProj₂
      x ← mkCompose pr₂ pr₁
      let y = pr₂
      body ← mkΔ x y
      lam₁ ← mkCurry body
      lam₂ ← mkCurry lam₁
      buildApplication n pat lam₂ args

  buildMorphism n pat (def (quote MonoidalSyntax.unpack⊗) (o ∷ m ∷ C ∷ mon ∷ A ∷ B ∷ p ⟨∷⟩ [])) =
    buildMorphism n pat p
  buildMorphism n pat (def (quote MonoidalSyntax.pack⊗) (o ∷ m ∷ C ∷ mon ∷ A ∷ B ∷ p ⟨∷⟩ [])) =
    buildMorphism n pat p

  buildMorphism n pat (def (quote MonoidalSyntax.`tt) args) = getε

  buildMorphism n pat (def (quote proj₁) (a ∷ b ∷ A ∷ B ∷ x ⟨∷⟩ [])) =
    do
      x′ ← buildMorphism n pat x
      mkProj₁ x′

  buildMorphism n pat (def (quote proj₂) (a ∷ b ∷ A ∷ B ∷ x ⟨∷⟩ [])) =
    do
      x′ ← buildMorphism n pat x
      mkProj₂ x′

  buildMorphism n pat (def (quote CartesianSyntax.let-in) (o ∷ m ∷ C ∷ cart ∷ a ∷ A ∷ B ∷ lam visible (abs nm body) ⟨∷⟩ x ⟨∷⟩ [])) =
    do
      body′ ← buildMorphism (suc n) (con (quote _,_) (weakenPat 1 pat ⟨∷⟩ var 0 ⟨∷⟩ [])) body
      x′ ← buildMorphism n pat x
      augmentEnv ← mkΔ id x′
      mkCompose body′ augmentEnv

  buildMorphism n pat (lam visible (abs nm body)) =
    do
      x′ ← buildMorphism (suc n) (con (quote _,_) (weakenPat 1 pat ⟨∷⟩ var 0 ⟨∷⟩ [])) body
      mkCurry x′

  buildMorphism n pat (def (quote ClosedSyntax._`$_) (o ∷ m ∷ C ∷ closed ∷ A ∷ B ∷ f ⟨∷⟩ args)) =
    do
      f′ ← buildMorphism n pat f
      buildApplication n pat f′ args

  buildMorphism n pat (def (quote ClosedSyntax.pack↝) (o ∷ m ∷ C ∷ closed ∷ A ∷ B ∷ f ⟨∷⟩ [])) = buildMorphism n pat f

  buildMorphism n pat (var i []) = do
    just t ← findVar pat i
     where
      nothing → lift $ typeError (strErr "Captured variable from outer context: " ∷ strErr (ℕ.show i) ∷ [])
    return t

  buildMorphism n pat tm = do
    -- To get the AST constructors printed rather rather than the pretty syntax
    quoted ← lift $ quoteTC (trimTerm 2 tm)
    norm ← lift $ normalise quoted
    lift $ debugPrint "cat" 2 (strErr "Unsupported body AST: " ∷ termErr norm ∷ [])
    lift $ typeError
      ( strErr "Unsupported: "
      ∷ termErr (pat-lam ((clause (proj₂ (guessTelescope 0 pat)) (vArg pat ∷ []) tm) ∷ []) [])
      ∷ []
      )

module _ where
  open RawMonad (TCM.monad {Level.zero})

  translate
    : ∀ {o m ℓ}
    → (C : Category o m ℓ)
    → {A B : ObjDesc C}
    → Translation
    → (interp C A → interp C B)
    → Term
    → TC ⊤
  translate C {A} {B} tr f hole = do
    let open Category C
    resultTy ← quoteTC (interpAsObj C A ⇒ interpAsObj C B)

    ctx ← getContext
    debugPrint "cat" 2 (List.concatMap (λ { (arg nm t) → strErr "\n" ∷ termErr t ∷ [] } ) ctx)

    debugPrint "cat" 2 (strErr "Type: " ∷ termErr resultTy ∷ [])

    tm₀ ← quoteTC f

    debugPrint "cat" 2 (strErr "Initial term: " ∷ termErr tm₀ ∷ [])

    lamTy ← quoteTC (interp C A → interp C B)
    tm ← checkType tm₀ lamTy

    -- debugPrint "cat" 2 (strErr "Checked term: " ∷ termErr tm ∷ [])

    lam visible (abs _ body) ← return $ η-expand visible tm
      where t → typeError (strErr "Expected η-expand to give a lambda: " ∷ termErr t ∷ [])

    bodySyn ← quoteTC body
    debugPrint "cat" 4 (strErr "Checked body AST: " ∷ termErr bodySyn ∷ [])

    result′ ← buildMorphism 1 (var 0) body tr
    result ← toTerm result′ tr

    debugPrint "cat" 2 (strErr "Result: " ∷ termErr result ∷ [])

    result1 ← checkType result resultTy
    unify result1 hole

    return tt

  macro
    ccc!
      : ∀ {o m ℓ} {C : Category o m ℓ} {A B : ObjDesc C}
      → CartesianClosed C
      → (interp C A → interp C B)
      → Term
      → TC ⊤
    ccc! ccc f hole = do
      tr ← buildCCC ccc
      translate _ tr f hole

    cc!
      : ∀ {o m ℓ} {C : Category o m ℓ} {A B : ObjDesc C}
      → Cartesian C
      → (interp C A → interp C B)
      → Term
      → TC ⊤
    cc! cc f hole = do
      tr ← buildCC cc
      translate _ tr f hole
