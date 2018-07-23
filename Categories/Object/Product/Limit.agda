open import Categories.Category

module Categories.Object.Product.Limit {o ℓ e} (C : Category o ℓ e) where

open import Level using (_⊔_)
open import Function hiding (_∘_; id)
open import Data.Product using (Σ; _,_)

open Category C
open import Categories.Limit
open import Categories.Discrete
open LimitsOf
open import Categories.Functor using (Functor; _⟨_⟩₀; _⟨_⟩₁)
open import Categories.Object.Product C
open import Categories.Object.Terminal
open import Categories.Support.PropositionalEquality
open import Categories.Cone
open import Categories.Cones
open import Data.Empty
open import Data.Unit
open import Data.Fin
open ConeOver

Limit₂→Product : (J : Functor (Discreteₙ 2) C) → Limit J → Product (J ⟨ # 0 ⟩₀) (J ⟨ # 1 ⟩₀)
Limit₂→Product J lim = record
  { A×B = vertex
  ; π₁ = proj (# 0)
  ; π₂ = proj (# 1)
  ; ⟨_,_⟩ = λ {C′} x y → morph-product C′ x y
  ; commute₁ = commute₁
  ; commute₂ = commute₂
  ; universal = universal′
  }
 where
  open Limit lim

  conify-morphisms
    : ∀ (C′ : Obj)
    → C′ ⇒ (J ⟨ # 0 ⟩₀)
    → C′ ⇒ (J ⟨ # 1 ⟩₀)
    → ConeOver.Cone J
  conify-morphisms C′ f g =
    record
      { N = C′
      ; ψ = ψ
      ; commute = commute′
      }
    where
      ψ : (X : Fin 2) → C′ ⇒ J ⟨ X ⟩₀
      ψ zero       = f
      ψ (suc zero) = g
      ψ (suc (suc ()))

      .commute′
        : ∀ {X Y}
            (x≣y : X ≣ Y)
        → J ⟨ x≣y ⟩₁ ∘ ψ X ≡ ψ Y
      commute′ {X} ≣-refl = let open HomReasoning in
        begin
          (J ⟨ ≣-refl ⟩₁) ∘ ψ X
        ↕
          J ⟨ Category.id (Discreteₙ 2) ⟩₁ ∘ ψ X
        ↓⟨ ∘-resp-≡ˡ (Functor.identity J) ⟩
          id ∘ ψ X
        ↓⟨ identityˡ ⟩
          ψ X
        ∎

  morph-product
    : ∀ (C′ : Obj)
    → C′ ⇒ (J ⟨ # 0 ⟩₀)
    → C′ ⇒ (J ⟨ # 1 ⟩₀)
    → C′ ⇒ vertex
  morph-product C′ f g = rep $ conify-morphisms C′ f g

  .commute₁
    : ∀ {A : Obj}
        {f : A ⇒ (J ⟨ # 0 ⟩₀)}
        {g : A ⇒ (J ⟨ # 1 ⟩₀)}
    → proj (# 0) ∘ morph-product A f g ≡ f
  commute₁ {A} {f} {g} = Limit.commute lim (conify-morphisms A f g) (# 0)

  .commute₂
    : ∀ {A : Obj}
        {f : A ⇒ (J ⟨ # 0 ⟩₀)}
        {g : A ⇒ (J ⟨ # 1 ⟩₀)}
    → proj (# 1) ∘ morph-product A f g ≡ g
  commute₂ {A} {f} {g} = Limit.commute lim (conify-morphisms A f g) (# 1)

  .universal′
    : ∀ {A}
        {f : A ⇒ (J ⟨ # 0 ⟩₀)}
        {g : A ⇒ (J ⟨ # 1 ⟩₀)}
        {i : A ⇒ vertex}
    → proj (# 0) ∘ i ≡ f
    → proj (# 1) ∘ i ≡ g
    → morph-product A f g ≡ i
  universal′ {A} {f} {g} π₁∘i≡f π₂∘i≡g = universal $ record
      { N-≣ = ≣-refl
      ; ψ-≡ = λ { zero → Heterogeneous.≡⇒∼ π₁∘i≡f
                ; (suc zero) → Heterogeneous.≡⇒∼ π₂∘i≡g
                ; (suc (suc ()))
                }
      }
    where cone = conify-morphisms A f g

Product→Limit₂ : ∀ {A B} → Product A B → (Σ (Functor (Discreteₙ 2) C) Limit)
Product→Limit₂ {A} {B} prod = J , lim
 where
  open Product prod

  J : Functor (Discreteₙ 2) C
  J = record
    { F₀ = λ { zero → A; (suc zero) → B; (suc (suc ())) }
    ; F₁ = λ { ≣-refl → id }
    ; identity = Equiv.refl
    ; homomorphism = λ { {_} {_} {_} {≣-refl} {≣-refl} → Equiv.sym identityˡ }
    ; F-resp-≡ = λ { {_} {_} {≣-refl} {≣-refl} _ → Equiv.refl}
    }

  lim : Limit J
  lim = record
    { terminal = record
      { ⊤ = ⊤-cone
      ; ! = λ {cone} → record
        { f = ⟨ Cone.ψ cone (# 0) , Cone.ψ cone (# 1) ⟩
        ; commute = λ { {zero} → Equiv.sym commute₁
                      ; {suc zero} → Equiv.sym commute₂
                      ; {suc (suc ())}
                      }
        }
      ; !-unique = !-unique
      }
    }
   where
    ψ : (X : Fin 2) → A×B ⇒ J ⟨ X ⟩₀
    ψ (zero) = π₁
    ψ (suc zero) = π₂
    ψ (suc (suc ()))

    ⊤-cone : ConeOver.Cone J
    ⊤-cone = record
      { N = A×B
      ; ψ = ψ
      ; commute = λ { ≣-refl → identityˡ }
      }

    .!-unique
      : ∀ {cone : ConeOver.Cone J}
          (f : ConeMorphism cone ⊤-cone) →
          ⟨ Cone.ψ cone (# 0) , (Cone.ψ cone (# 1)) ⟩ ≡ (ConeMorphism.f f)
    !-unique {cone} f = let open HomReasoning in
      begin
        ⟨ Cone.ψ cone (# 0) , (Cone.ψ cone (# 1)) ⟩
      ↓⟨ ⟨⟩-cong₂ (ConeMorphism.commute f) (ConeMorphism.commute f) ⟩
        ⟨ π₁ ∘ ConeMorphism.f f , π₂ ∘ ConeMorphism.f f ⟩
      ↓⟨ g-η ⟩
        (ConeMorphism.f f)
      ∎
