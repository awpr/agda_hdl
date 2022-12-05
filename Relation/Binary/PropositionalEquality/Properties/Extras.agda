module Relation.Binary.PropositionalEquality.Properties.Extras where

open import Function using (_∘_; id)
open import Level using (Level)

open import Relation.Binary using (REL; Rel)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.Properties public
open import Relation.Unary using (Pred)

private
  variable
    a b c p ℓ : Level
    A : Set a
    B : Set b
    C : Set c

-- subst and subst₂ distribute over "nullary functions" of the equated
-- terms i.e. constants.  That is, needless uses of subst and subst₂
-- can be discarded.

subst-dist₀
  : ∀ {x : A} {y₁ y₂ : B} {y₁≡y₂ : y₁ ≡ y₂}
  → subst (λ _ → A) y₁≡y₂ x ≡ x
subst-dist₀ {y₁≡y₂ = refl} = refl

subst₂-dist₀
  : ∀ {x : A}
      {y₁ y₂ : B} {y₁≡y₂ : y₁ ≡ y₂}
      {z₁ z₂ : C} {z₁≡z₂ : z₁ ≡ z₂}
  → subst₂ (λ _ _ → A) y₁≡y₂ z₁≡z₂ x ≡ x
subst₂-dist₀ {y₁≡y₂ = refl} {z₁≡z₂ = refl} = refl

-- subst and subst₂ distribute over unary dependent function
-- applications of the equated terms.  subst-dist₁ is almost the same
-- as subst-application, but without the extra `cong f`.  (It's the
-- same as subst-application′ in unreleased stlib-suc(1.7.1)).

subst-dist₁
  : ∀ (C : A → Set c) {P : Pred A p}
      {x₁ x₂ : A} {v : C x₁}
  → (g : ∀ x → C x → P x)
  → (x₁≡x₂ : x₁ ≡ x₂)
  → subst P x₁≡x₂ (g x₁ v) ≡ g x₂ (subst C x₁≡x₂ v)
subst-dist₁ _ _ refl = refl

subst₂-dist₁
  : ∀ (C : A → B → Set c)  {_~_ : REL A B ℓ}
      {x₁ x₂ : A} {y₁ y₂ : B} {v : C x₁ y₁}
  → (g : ∀ x y → C x y → x ~ y)
  → (x₁≡x₂ : x₁ ≡ x₂)
  → (y₁≡y₂ : y₁ ≡ y₂)
  → subst₂ _~_ x₁≡x₂ y₁≡y₂ (g x₁ y₁ v) ≡ g x₂ y₂ (subst₂ C x₁≡x₂ y₁≡y₂ v)
subst₂-dist₁ _ _ refl refl = refl

subst₂-dist₁ʳ
  : ∀ {a₂ b₂} {A₂ : Set a₂} {B₂ : Set b₂}
      {f₁ : A → A₂} {f₂ : B → B₂}
      (C : A → B → Set c) {_~_ : REL A₂ B₂ ℓ}
      {x₁ x₂ : A} {y₁ y₂ : B} {v : C x₁ y₁}
  → (g : ∀ x y → C x y → f₁ x ~ f₂ y)
  → (x₁≡x₂ : x₁ ≡ x₂)
  → (y₁≡y₂ : y₁ ≡ y₂)
  → subst₂ _~_ (cong f₁ x₁≡x₂) (cong f₂ y₁≡y₂) (g x₁ y₁ v) ≡
      g x₂ y₂ (subst₂ C x₁≡x₂ y₁≡y₂ v)
subst₂-dist₁ʳ _ _ refl refl = refl

-- subst and subst₂ distribute over binary dependent function
-- applications of the equated terms.

subst-dist₂
  : ∀ {c₁ c₂}
      (C₁ : A → Set c₁) (C₂ : A → Set c₂) {P : A → Set p}
      {x₁ x₂ : A} {u : C₁ x₁}  {v : C₂ x₁}
  → (g : ∀ x → C₁ x → C₂ x → P x)
  → (x₁≡x₂ : x₁ ≡ x₂)
  → subst P x₁≡x₂ (g x₁ u v) ≡
      g x₂ (subst C₁ x₁≡x₂ u) (subst C₂ x₁≡x₂ v)
subst-dist₂ _ _ _ refl = refl

subst₂-dist₂
  : ∀ {c₁ c₂}
      (C₁ : A → B → Set c₁) (C₂ : A → B → Set c₂) {_~_ : REL A B ℓ}
      {x₁ x₂ : A} {y₁ y₂ : B} {u : C₁ x₁ y₁} {v : C₂ x₁ y₁}
  → (g : ∀ x y → C₁ x y → C₂ x y → x ~ y)
  → (x₁≡x₂ : x₁ ≡ x₂)
  → (y₁≡y₂ : y₁ ≡ y₂)
  → subst₂ _~_ x₁≡x₂ y₁≡y₂ (g x₁ y₁ u v) ≡
      g x₂ y₂ (subst₂ C₁ x₁≡x₂ y₁≡y₂ u) (subst₂ C₂ x₁≡x₂ y₁≡y₂ v)
subst₂-dist₂ _ _ _ refl refl = refl

-- subst₂ factors over "separable" binary dependent functions: if
-- each argument of `g` depends on only one of the equated terms, the
-- subst₂ simplifies to two substs.  This is the same as using
-- subst₂-dist₂ and then simplifying each resulting subst₂ with
-- e.g. subst₂-∘ and cong₂-reflˡ.
subst₂-factor
  : ∀ {c₁ c₂}
      (C₁ : A → Set c₁) (C₂ : B → Set c₂) {_~_ : REL A B ℓ}
      {x₁ x₂ : A} {u : C₁ x₁} {y₁ y₂ : B} {v : C₂ y₁}
  → (g : ∀ x y → C₁ x → C₂ y → x ~ y)
  → (x₁≡x₂ : x₁ ≡ x₂)
  → (y₁≡y₂ : y₁ ≡ y₂)
  → subst₂ _~_ x₁≡x₂ y₁≡y₂ (g x₁ y₁ u v) ≡
      g x₂ y₂ (subst C₁ x₁≡x₂ u) (subst C₂ y₁≡y₂ v)
subst₂-factor _ _ _ refl refl = refl

-- subst commutes past itself.
subst-comm
  : ∀ {x₁ x₂ : A} {y₁ y₂ : B}
  → (_~_ : REL A B ℓ)
  → {r : x₁ ~ y₁}
  → (x₁≡x₂ : x₁ ≡ x₂)
  → (y₁≡y₂ : y₁ ≡ y₂)
  → subst (_~ y₂) x₁≡x₂ (subst (x₁ ~_) y₁≡y₂ r) ≡
    subst (x₂ ~_) y₁≡y₂ (subst (_~ y₁) x₁≡x₂ r)
subst-comm _ refl refl = refl

-- subst, being a "weird" identity function, preserves every relation.
cong-subst
  : ∀ {P : A → Set p} {x₁ x₂ : A} {p q : P x₁} (_~_ : ∀ {x} → Rel (P x) ℓ)
  → (x₁≡x₂ : x₁ ≡ x₂)
  → p ~ q
  → subst P x₁≡x₂ p ~ subst P x₁≡x₂ q
cong-subst _ refl pq = pq

-- subst₂, being a "weird" identity function, preserves every relation.
cong-subst₂
  : ∀ {_~_ : A → B → Set p}
      {x₁ x₂ : A} {y₁ y₂ : B}
      {p q : x₁ ~ y₁}
      (_≈_ : ∀ {x y} → Rel (x ~ y) ℓ)
  → (x₁≡x₂ : x₁ ≡ x₂)
  → (y₁≡y₂ : y₁ ≡ y₂)
  → p ≈ q
  → subst₂ _~_ x₁≡x₂ y₁≡y₂ p ≈ subst₂ _~_ x₁≡x₂ y₁≡y₂ q
cong-subst₂ _ refl refl pq = pq

subst₂-subst₂
  : ∀ {x₁ x₂ x₃ : A} {y₁ y₂ y₃ : B} {_~_ : REL A B ℓ} {p : x₁ ~ y₁}
  → (x₁≡x₂ : x₁ ≡ x₂)
  → (x₂≡x₃ : x₂ ≡ x₃)
  → (y₁≡y₂ : y₁ ≡ y₂)
  → (y₂≡y₃ : y₂ ≡ y₃)
  → subst₂ _~_ x₂≡x₃ y₂≡y₃ (subst₂ _~_ x₁≡x₂ y₁≡y₂ p) ≡
      subst₂ _~_ (trans x₁≡x₂ x₂≡x₃) (trans y₁≡y₂ y₂≡y₃) p
subst₂-subst₂ refl refl refl refl = refl

subst-∘₂
  : ∀ {x y : A} {z w : B}
  → (P : C → Set p)
  → (f : A → B → C)
  → (x≡y : x ≡ y)
  → (z≡w : z ≡ w)
  → {r : P (f x z)}
  → subst₂ (λ x z → P (f x z)) x≡y z≡w r ≡ subst P (cong₂ f x≡y z≡w) r
subst-∘₂ _ _ refl refl = refl

subst₂-split
  : ∀ {_~_ : REL A B ℓ}
      {x₁ x₂ : A} {y₁ y₂ : B} {p : x₁ ~ y₁}
  → (x₁≡x₂ : x₁ ≡ x₂)
  → (y₁≡y₂ : y₁ ≡ y₂)
  → subst₂ _~_ x₁≡x₂ y₁≡y₂ p ≡ subst (_~ y₂) x₁≡x₂ (subst (x₁ ~_) y₁≡y₂ p)
subst₂-split refl refl = refl

subst₂-subst
  : ∀ (_~_ : Rel A ℓ) {x₁ x₂}
      {p : x₁ ~ x₁}
  → (x₁≡x₂ : x₁ ≡ x₂)
  → subst₂ _~_ x₁≡x₂ x₁≡x₂ p ≡ subst (λ x → x ~ x) x₁≡x₂ p
subst₂-subst _ refl = refl

sym-cong₂
  : ∀ {x₁ x₂ : A} {y₁ y₂ : B}
  → (f : A → B → C)
  → (x₁≡x₂ : x₁ ≡ x₂)
  → (y₁≡y₂ : y₁ ≡ y₂)
  → sym (cong₂ f x₁≡x₂ y₁≡y₂) ≡ cong₂ f (sym x₁≡x₂) (sym y₁≡y₂)
sym-cong₂ _ refl refl = refl

subst₂-fun
  : ∀ {A₁ A₂ : Set a} {B₁ B₂ : Set b}
  → (A₁≡A₂ : A₁ ≡ A₂)
  → (B₁≡B₂ : B₁ ≡ B₂)
  → (f : A₁ → B₁)
  → subst₂ (\A B → A → B) A₁≡A₂ B₁≡B₂ f ≗
      subst id B₁≡B₂ ∘ f ∘ subst id (sym A₁≡A₂)
subst₂-fun refl refl f x = refl
