module Categories.Syntax.Cartesian.Functors where

open import Data.List as List using ([]; _∷_)
import Data.List.Properties as List
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (⊤)
open import Level using (Level)
open import Function using (_∘_; id; _$_; flip)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality.Extras as ≡ using
  ( _≡_; refl; _≗_; cast
  ; cong; cong₂; subst; subst₂; sym; trans
  )
import Relation.Binary.PropositionalEquality.WithK as ≡
import Relation.Binary.PropositionalEquality.Properties.Extras as ≡

open import Categories.Cartesian using (CartesianCategory)
open import Categories.Category using (Category)
open import Categories.Category.Types using (→CC′)
open import Categories.Functor using (Functor; _○_)
open import Categories.PolyQuiver using
  ( PolyQuiver; PQMorphism; _∘M_; ccToPolyQuiver; wrap; toCCObj; toCCObj₁
  )
import Categories.Syntax.Cartesian as Syntax
open import Categories.Syntax.Cartesian.Core

open Categories.Functor.FunctorOperators

private
  variable
    o m ℓ o₁ m₁ ℓ₁ o₂ m₂ ℓ₂ o₃ m₃ ℓ₃ : Level
    Q : PolyQuiver o₁ m₁ ℓ₁
    R : PolyQuiver o₂ m₂ ℓ₂
    S : PolyQuiver o₃ m₃ ℓ₃

module _ (CC : CartesianCategory o m ℓ) where
  private module C = CartesianCategory CC

  private
    CQ : PolyQuiver o m ℓ
    CQ = ccToPolyQuiver CC

    module CQ = Syntax CQ

  flatten₀ : CQ.Obj → C.Obj
  flatten₀ (prim A) = A
  flatten₀ 𝟏 = C.⋆
  flatten₀ (A ⊗ B) = flatten₀ A C.× flatten₀ B

  toCC₁-flatten : ∀ A₁ As → toCCObj₁ CC A₁ As ≡ flatten₀ (toObj₁ A₁ As)
  toCC₁-flatten A₁ [] = refl
  toCC₁-flatten A₁ (A₂ ∷ As) = cong₂ C._×_ refl (toCC₁-flatten A₂ As)

  toCC-flatten : toCCObj CC ≗ flatten₀ Function.∘ toObj
  toCC-flatten [] = refl
  toCC-flatten (A₁ ∷ As) = toCC₁-flatten A₁ As

  flatten₁ : ∀ {A B} → A CQ.⇒ B → flatten₀ A C.⇒ flatten₀ B
  flatten₁ (prim {As} {Bs} (wrap f)) = subst₂ C._⇒_ (toCC-flatten As) (toCC-flatten Bs) f
  flatten₁ id = C.id
  flatten₁ (f ∘ g) = flatten₁ f C.∘ flatten₁ g
  flatten₁ (f △ g) = flatten₁ f C.△ flatten₁ g
  flatten₁ p₁ = C.p₁
  flatten₁ p₂ = C.p₂
  flatten₁ ε = C.ε

  flatten₁-resp-≈
    : ∀ {A B} {f g : A CQ.⇒ B}
    → f CQ.≈ g
    → flatten₁ f C.≈ flatten₁ g
  flatten₁-resp-≈ (CQ.prim {As} {Bs} f₁≈f₂) =
    ≡.cong-subst₂ C._≈_ (toCC-flatten As) (toCC-flatten Bs) f₁≈f₂
  flatten₁-resp-≈ CQ.id = C.≈.refl
  flatten₁-resp-≈ (f₁≈f₂ CQ.∘ g₁≈g₂) =
    C.∘-resp-≈ (flatten₁-resp-≈ f₁≈f₂) (flatten₁-resp-≈ g₁≈g₂)
  flatten₁-resp-≈ CQ.p₁ = C.≈.refl
  flatten₁-resp-≈ CQ.p₂ = C.≈.refl
  flatten₁-resp-≈ CQ.ε-unique = C.ε-unique
  flatten₁-resp-≈ (CQ.≈-sym eq) = C.≈.sym (flatten₁-resp-≈ eq)
  flatten₁-resp-≈ (CQ.≈-trans eq₁ eq₂) =
    C.≈.trans (flatten₁-resp-≈ eq₁) (flatten₁-resp-≈ eq₂)
  flatten₁-resp-≈ (CQ.△-unique p₁≈f p₂≈g) =
    C.△-unique (flatten₁-resp-≈ p₁≈f) (flatten₁-resp-≈ p₂≈g)
  flatten₁-resp-≈ (CQ.△-factors-p₁) = C.△-factors-p₁
  flatten₁-resp-≈ (CQ.△-factors-p₂) = C.△-factors-p₂
  flatten₁-resp-≈ CQ.∘-idˡ = C.∘-idˡ
  flatten₁-resp-≈ CQ.∘-idʳ = C.∘-idʳ
  flatten₁-resp-≈ CQ.∘-assocˡ = C.∘-assocˡ

  flatten : Functor CQ.⇒Cat C.𝓤
  flatten = record
    { map₀ = flatten₀
    ; map₁ = flatten₁
    ; map₁-resp-≈ = flatten₁-resp-≈
    ; map₁-id = C.≈.refl
    ; map₁-∘ = C.≈.refl
    }

module _ (M : PQMorphism Q R) where
  private module Q = Syntax Q
  private module R = Syntax R
  private module M = PQMorphism M

  mapSyntax₀ : Q.Obj → R.Obj
  mapSyntax₀ (prim A) = prim (M.map₀ A)
  mapSyntax₀ 𝟏 = 𝟏
  mapSyntax₀ (A ⊗ B) = mapSyntax₀ A ⊗ mapSyntax₀ B

  toObj₁-mapSyntax₀
    : ∀ A₁ As
    → toObj₁ (M.map₀ A₁) (List.map M.map₀ As) ≡ mapSyntax₀ (toObj₁ A₁ As)
  toObj₁-mapSyntax₀ A₁ [] = refl
  toObj₁-mapSyntax₀ A₁ (A₂ ∷ As) = cong₂ R._⊗_ refl (toObj₁-mapSyntax₀ A₂ As)

  toObj-mapSyntax₀ : ∀ As → toObj (List.map M.map₀ As) ≡ mapSyntax₀ (toObj As)
  toObj-mapSyntax₀ [] = refl
  toObj-mapSyntax₀ (A₁ ∷ As) = toObj₁-mapSyntax₀ A₁ As

  mapSyntax₁ : ∀ {A B} → A Q.⇒ B → mapSyntax₀ A R.⇒ mapSyntax₀ B
  mapSyntax₁ (Q.prim {As} {Bs} x) =
    subst₂ R._⇒_ (toObj-mapSyntax₀ As) (toObj-mapSyntax₀ Bs) (R.prim (M.map₁ x))
  mapSyntax₁ Q.id = R.id
  mapSyntax₁ (f Q.∘ g) = mapSyntax₁ f R.∘ mapSyntax₁ g
  mapSyntax₁ (f Q.△ g) = mapSyntax₁ f R.△ mapSyntax₁ g
  mapSyntax₁ Q.p₁ = R.p₁
  mapSyntax₁ Q.p₂ = R.p₂
  mapSyntax₁ Q.ε = R.ε

  mapSyntax₁-resp-≈
    : ∀ {A B} {f g : A Q.⇒ B}
    → f Q.≈ g
    → mapSyntax₁ f R.≈ mapSyntax₁ g
  mapSyntax₁-resp-≈ (Q.prim f₁≈f₂) =
    ≡.cong-subst₂ R._≈_ _ _ (R.prim (M.map₁-resp-≈ f₁≈f₂))
  mapSyntax₁-resp-≈ Q.id = R.id
  mapSyntax₁-resp-≈ (f₁≈f₂ Q.∘ g₁≈g₂) =
    mapSyntax₁-resp-≈ f₁≈f₂ R.∘ mapSyntax₁-resp-≈ g₁≈g₂
  mapSyntax₁-resp-≈ (Q.△-unique p₁≈f p₂≈g) =
    R.△-unique (mapSyntax₁-resp-≈ p₁≈f) (mapSyntax₁-resp-≈ p₂≈g)
  mapSyntax₁-resp-≈ Q.p₁ = R.p₁
  mapSyntax₁-resp-≈ Q.p₂ = R.p₂
  mapSyntax₁-resp-≈ Q.ε-unique = R.ε-unique
  mapSyntax₁-resp-≈ (Q.≈-sym eq) = R.≈-sym (mapSyntax₁-resp-≈ eq)
  mapSyntax₁-resp-≈ (Q.≈-trans eq₁ eq₂) =
    R.≈-trans (mapSyntax₁-resp-≈ eq₁) (mapSyntax₁-resp-≈ eq₂)
  mapSyntax₁-resp-≈ Q.△-factors-p₁ = R.△-factors-p₁
  mapSyntax₁-resp-≈ Q.△-factors-p₂ = R.△-factors-p₂
  mapSyntax₁-resp-≈ Q.∘-idˡ = R.∘-idˡ
  mapSyntax₁-resp-≈ Q.∘-idʳ = R.∘-idʳ
  mapSyntax₁-resp-≈ Q.∘-assocˡ = R.∘-assocˡ

  mapSyntax : Functor Q.⇒Cat R.⇒Cat
  mapSyntax = record
    { map₀ = mapSyntax₀
    ; map₁ = mapSyntax₁
    ; map₁-resp-≈ = mapSyntax₁-resp-≈
    ; map₁-id = R.≈-refl
    ; map₁-∘ = R.≈-refl
    }

module _
    (M : PQMorphism Q R)
    (N : PQMorphism Q R)
    (M₀≗N₀ : PQMorphism.map₀ M ≗ PQMorphism.map₀ N)
    where
  private
    module Q = PolyQuiver Q
    module R = PolyQuiver R
    module M = PQMorphism M
    module N = PQMorphism N
    module SQ = Syntax Q
    module SR = Syntax R
    open Category.≈-Reasoning SR.⇒Cat

  map₀-resp-≗ : mapSyntax M ₀_ ≗ mapSyntax N ₀_
  map₀-resp-≗ (SQ.prim A) = cong prim (M₀≗N₀ A)
  map₀-resp-≗ SQ.𝟏 = refl
  map₀-resp-≗ (A SQ.⊗ B) = cong₂ _⊗_ (map₀-resp-≗ A) (map₀-resp-≗ B)

  module _
      (M₁≈N₁
        : ∀ {As Bs} (f : Syntax.Mor Q As Bs)
        → (subst₂ R._⇒_
            (List.map-cong M₀≗N₀ As)
            (List.map-cong M₀≗N₀ Bs)
            (M.map₁ f)) R.≈
          N.map₁ f)
      where

    map₁-resp-≗
      : ∀ {A B}
      → (f : A SQ.⇒ B)
      → subst₂ SR._⇒_ (map₀-resp-≗ A) (map₀-resp-≗ B) (mapSyntax M ₁ f) SR.≈
          mapSyntax N ₁ f
    map₁-resp-≗ (prim {As} {Bs} f) =
      begin
        subst₂ SR._⇒_ (map₀-resp-≗ (toObj As)) (map₀-resp-≗ (toObj Bs))
          (subst₂ SR._⇒_ (toObj-mapSyntax₀ M As) (toObj-mapSyntax₀ M Bs)
            (SR.prim (M.map₁ f)))

      ≡⟨ ≡.subst₂-subst₂ (toObj-mapSyntax₀ M As) (map₀-resp-≗ (toObj As)) _ _ ⟩
        subst₂ SR._⇒_
          (≡.trans (toObj-mapSyntax₀ M As) (map₀-resp-≗ (toObj As)))
          (≡.trans (toObj-mapSyntax₀ M Bs) (map₀-resp-≗ (toObj Bs)))
          (SR.prim (M.map₁ f))

      ≡⟨ cong₂
          (λ x y → subst₂ SR._⇒_ x y (SR.prim (M.map₁ f)))
          (≡.≡-irrelevant _ _)
          (≡.≡-irrelevant _ _) ⟩
        subst₂ SR._⇒_
          (≡.trans (cong SR.toObj (List.map-cong M₀≗N₀ As)) (toObj-mapSyntax₀ N As))
          (≡.trans (cong SR.toObj (List.map-cong M₀≗N₀ Bs)) (toObj-mapSyntax₀ N Bs))
          (SR.prim (M.map₁ f))

      ≡˘⟨ ≡.subst₂-subst₂
            (cong SR.toObj (List.map-cong M₀≗N₀ As))
            (toObj-mapSyntax₀ N As)
            _ _ ⟩
        subst₂ SR._⇒_ (toObj-mapSyntax₀ N As) (toObj-mapSyntax₀ N Bs)
          (subst₂ SR._⇒_
            (cong SR.toObj (List.map-cong M₀≗N₀ As))
            (cong SR.toObj (List.map-cong M₀≗N₀ Bs))
            (SR.prim (M.map₁ f)))

      ≡⟨ ≡.cong-subst₂ _≡_
            (toObj-mapSyntax₀ N As)
            (toObj-mapSyntax₀ N Bs)
            (SR.subst₂-dist-prim _ _) ⟩
        subst₂ SR._⇒_ (toObj-mapSyntax₀ N As) (toObj-mapSyntax₀ N Bs)
          (SR.prim
          (subst₂ R._⇒_ (List.map-cong M₀≗N₀ As) (List.map-cong M₀≗N₀ Bs)
            (M.map₁ f)))

      ≈⟨ ≡.cong-subst₂ SR._≈_
          (toObj-mapSyntax₀ N As)
          (toObj-mapSyntax₀ N Bs)
          (SR.prim (M₁≈N₁ f)) ⟩
        subst₂ SR._⇒_ (toObj-mapSyntax₀ N As) (toObj-mapSyntax₀ N Bs)
          (SR.prim (N.map₁ f))
      ∎

    map₁-resp-≗ (f SR.∘ g) =
      begin
        subst₂ (Morphism SR.Mor) (map₀-resp-≗ _) (map₀-resp-≗ _)
          (mapSyntax₁ M f SR.∘ mapSyntax₁ M g)

      ≡⟨ SR.subst₂-dist-∘ _ _ _ ⟩
        subst₂ (Morphism SR.Mor) (map₀-resp-≗ _) (map₀-resp-≗ _) (mapSyntax₁ M f) SR.∘
        subst₂ (Morphism SR.Mor) (map₀-resp-≗ _) (map₀-resp-≗ _) (mapSyntax₁ M g)

      ≈⟨ map₁-resp-≗ f SR.∘ map₁-resp-≗ g ⟩
        mapSyntax₁ N f SR.∘ mapSyntax₁ N g
      ∎

    map₁-resp-≗ (f △ g) =
      begin
        subst₂ SR._⇒_ (map₀-resp-≗ _)
          (cong₂ SR._⊗_ (map₀-resp-≗ _) (map₀-resp-≗ _))
          (mapSyntax₁ M f SR.△ mapSyntax₁ M g)

      ≡⟨ SR.subst₂-dist-△ _ _ _ ⟩
        subst₂ SR._⇒_ (map₀-resp-≗ _) (map₀-resp-≗ _) (mapSyntax₁ M f) SR.△
        subst₂ SR._⇒_ (map₀-resp-≗ _) (map₀-resp-≗ _) (mapSyntax₁ M g)

      ≈⟨ SR.△-resp-≈ (map₁-resp-≗ f) (map₁-resp-≗ g) ⟩
        mapSyntax₁ N f SR.△ mapSyntax₁ N g
      ∎

    map₁-resp-≗ SR.id = SR.≈-reflexive (SR.subst₂-dist-id _)
    map₁-resp-≗ p₁ = SR.≈-reflexive (SR.subst₂-dist-p₁ _ _)
    map₁-resp-≗ p₂ = SR.≈-reflexive (SR.subst₂-dist-p₂ _ _)
    map₁-resp-≗ ε = SR.≈-reflexive (SR.subst₂-dist-ε _)

    map₁-pointwise
      : ∀ {A B} {f g : Syntax._⇒_ Q A B}
      → f SQ.≈ g
      → (subst₂ (Syntax._⇒_ R)
          (map₀-resp-≗ A)
          (map₀-resp-≗ B)
          (mapSyntax M ₁ f)) SR.≈
        (mapSyntax N ₁ g)
    map₁-pointwise {f = f} {g} f≈g =
      begin subst₂ SR._⇒_ _ _ (mapSyntax₁ M f)
      ≈⟨ map₁-resp-≗ f ⟩ mapSyntax₁ N f
      ≈⟨ mapSyntax₁-resp-≈ N f≈g ⟩ mapSyntax₁ N g
      ∎

module _ (M : PQMorphism R S) (N : PQMorphism Q R) where
  private
    module Q = Syntax Q
    module R = Syntax R
    module S = Syntax S
    module M = PQMorphism M
    module N = PQMorphism N

  open ≡.≡-Reasoning

  map∘map₀≗map₀ : (mapSyntax M ○ mapSyntax N) ₀_ ≗ mapSyntax (M ∘M N) ₀_
  map∘map₀≗map₀ (prim _) = refl
  map∘map₀≗map₀ 𝟏 = refl
  map∘map₀≗map₀ (A ⊗ B) = cong₂ _⊗_ (map∘map₀≗map₀ A) (map∘map₀≗map₀ B)


  map∘map₁≗map₁
    : {A B : Q.Obj}
    → (f : A Q.⇒ B)
    → subst₂ S._⇒_ (map∘map₀≗map₀ A) (map∘map₀≗map₀ B) ((mapSyntax M ○ mapSyntax N) ₁ f) ≡
        mapSyntax (M ∘M N) ₁ f
  map∘map₁≗map₁ (Q.prim {As} {Bs} x) =
    begin
      subst₂ S._⇒_
        (map∘map₀≗map₀ (Q.toObj As))
        (map∘map₀≗map₀ (Q.toObj Bs))
        (mapSyntax₁ M
          (subst₂ R._⇒_
            (toObj-mapSyntax₀ N As)
            (toObj-mapSyntax₀ N Bs)
            (prim (N.map₁ x))))

    ≡˘⟨ ≡.cong-subst₂ _≡_
         (map∘map₀≗map₀ (Q.toObj As))
         (map∘map₀≗map₀ (Q.toObj Bs))
         (≡.subst₂-dist₁ʳ R._⇒_
           (λ _ _ → mapSyntax₁ M)
           (toObj-mapSyntax₀ N As)
           (toObj-mapSyntax₀ N Bs)) ⟩
      subst₂ S._⇒_
        (map∘map₀≗map₀ (Q.toObj As))
        (map∘map₀≗map₀ (Q.toObj Bs))
        (subst₂ S._⇒_
          (cong (mapSyntax₀ M) (toObj-mapSyntax₀ N As))
          (cong (mapSyntax₀ M) (toObj-mapSyntax₀ N Bs))
          (subst₂ S._⇒_
             (toObj-mapSyntax₀ M (List.map N.map₀ As))
             (toObj-mapSyntax₀ M (List.map N.map₀ Bs))
             (prim (M.map₁ (N.map₁ x)))))

    ≡⟨ ≡.subst₂-subst₂
         (cong (mapSyntax₀ M) (toObj-mapSyntax₀ N As))
         (map∘map₀≗map₀ (Q.toObj As))
         _ _ ⟩
      subst₂ S._⇒_
        (trans
          (cong (mapSyntax₀ M) (toObj-mapSyntax₀ N As))
          (map∘map₀≗map₀ (Q.toObj As)))
        (trans
          (cong (mapSyntax₀ M) (toObj-mapSyntax₀ N Bs))
          (map∘map₀≗map₀ (Q.toObj Bs)))
        (subst₂ S._⇒_
          (toObj-mapSyntax₀ M (List.map N.map₀ As))
          (toObj-mapSyntax₀ M (List.map N.map₀ Bs))
          (prim (M.map₁ (N.map₁ x))))

    ≡⟨ ≡.subst₂-subst₂
         (toObj-mapSyntax₀ M (List.map N.map₀ As))
         (trans
           (cong (mapSyntax₀ M) (toObj-mapSyntax₀ N As))
           (map∘map₀≗map₀ (Q.toObj As)))
         _
         _ ⟩
      subst₂ S._⇒_
        (trans
          (toObj-mapSyntax₀ M (List.map N.map₀ As))
          (trans
            (cong (mapSyntax₀ M) (toObj-mapSyntax₀ N As))
            (map∘map₀≗map₀ (Q.toObj As))))
        (trans
          (toObj-mapSyntax₀ M (List.map N.map₀ Bs))
          (trans
            (cong (mapSyntax₀ M) (toObj-mapSyntax₀ N Bs))
            (map∘map₀≗map₀ (Q.toObj Bs))))
        (prim (M.map₁ (N.map₁ x)))

    ≡⟨ cong₂
         (λ X Y → subst₂ S._⇒_ X Y (prim (M.map₁ (N.map₁ x))))
         (≡.≡-irrelevant _ _)
         (≡.≡-irrelevant _ _)  ⟩
      subst₂ S._⇒_
        (trans
          (cong S.toObj (sym (List.map-compose As)))
          (toObj-mapSyntax₀ (M ∘M N) As))
        (trans
          (cong S.toObj (sym (List.map-compose Bs)))
          (toObj-mapSyntax₀ (M ∘M N) Bs))
        (prim (M.map₁ (N.map₁ x)))

    ≡˘⟨ ≡.subst₂-subst₂
          (cong S.toObj (sym (List.map-compose As)))
          (toObj-mapSyntax₀ (M ∘M N) As)
           _ _ ⟩
      subst₂ S._⇒_
        (toObj-mapSyntax₀ (M ∘M N) As)
        (toObj-mapSyntax₀ (M ∘M N) Bs)
        (subst₂ S._⇒_
           (cong S.toObj (sym (List.map-compose As)))
           (cong S.toObj (sym (List.map-compose Bs)))
           (prim (M.map₁ (N.map₁ x))))

    ≡⟨ ≡.cong-subst₂ _≡_
         (toObj-mapSyntax₀ (M ∘M N) As)
         (toObj-mapSyntax₀ (M ∘M N) Bs)
         (S.subst₂-dist-prim
           (sym (List.map-compose As))
           (sym (List.map-compose Bs))) ⟩
      subst₂ S._⇒_
        (toObj-mapSyntax₀ (M ∘M N) As)
        (toObj-mapSyntax₀ (M ∘M N) Bs)
        (prim
         (subst₂ S.Mor (sym (List.map-compose _)) (sym (List.map-compose _))
          (M.map₁ (N.map₁ x))))
    ∎

  map∘map₁≗map₁ Q.id = S.subst₂-dist-id _
  map∘map₁≗map₁ Q.p₁ = S.subst₂-dist-p₁ _ _
  map∘map₁≗map₁ Q.p₂ = S.subst₂-dist-p₂ _ _
  map∘map₁≗map₁ Q.ε = S.subst₂-dist-ε _

  map∘map₁≗map₁ (f Q.∘ g) =
    begin
      subst₂ S._⇒_ _ _
        ((mapSyntax M ○ mapSyntax N) ₁ f S.∘ (mapSyntax M ○ mapSyntax N) ₁ g)

    ≡⟨ S.subst₂-dist-∘ _ _ _ ⟩
      subst₂ S._⇒_ _ _ (mapSyntax M ○ mapSyntax N ₁$ f) S.∘
      subst₂ S._⇒_ _ _ (mapSyntax M ○ mapSyntax N ₁$ g)

    ≡⟨ cong₂ S._∘_ (map∘map₁≗map₁ f) (map∘map₁≗map₁ g) ⟩
      mapSyntax (M ∘M N) ₁ f S.∘ (mapSyntax (M ∘M N) ₁ g)
    ∎

  map∘map₁≗map₁ (f Q.△ g) =
    begin
      subst₂ S._⇒_ _ _
        ((mapSyntax M ○ mapSyntax N) ₁ f S.△ (mapSyntax M ○ mapSyntax N) ₁ g)

    ≡⟨ S.subst₂-dist-△ _ _ _ ⟩
      subst₂ S._⇒_ _ _ (mapSyntax M ○ mapSyntax N ₁$ f) S.△
        subst₂ S._⇒_ _ _ (mapSyntax M ○ mapSyntax N ₁$ g)

    ≡⟨ cong₂ S._△_ (map∘map₁≗map₁ f) (map∘map₁≗map₁ g) ⟩
      mapSyntax (M ∘M N) ₁ f S.△ mapSyntax (M ∘M N) ₁ g
    ∎
