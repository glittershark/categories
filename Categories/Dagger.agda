module Categories.Dagger where

open import Level

open import Categories.Category
open import Categories.Functor hiding (_≡_; id; _∘_)
open import Categories.Support.PropositionalEquality

replace : ∀ {ℓ} {A B : Set ℓ} → A ≣ B → A → B
replace ≣-refl a = a

record Dagger {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  open Category C
  open Equiv

  field
    _† : ∀ {A B} → A ⇒ B → B ⇒ A

    -- functor laws
    .identity     : ∀ {A : Obj}
                  → id {A} ≡ (id {A}) †
    .homomorphism : ∀ {A B C} (f : A ⇒ B) (g : B ⇒ C)
                  → (g ∘ f) † ≡ f † ∘ g †
    .resp-≡       : {A B : Obj} {f g : C [ A , B ]}
                  → f ≡ g
                  → f † ≡ g †

    .involutive   : ∀ {A B} (f : A ⇒ B)
                  → f † † ≡ f

  †-functor⃗ : Functor C op
  †-functor⃗ = record
    { F₀ = λ x → x
    ; F₁ = _†

    ; identity     = sym identity
    ; homomorphism = λ {_} {_} {_} {f} {g} → homomorphism f g
    ; F-resp-≡     = resp-≡
    }

  †-functor⃖ : Functor op C
  †-functor⃖ = record
    { F₀ = λ x → x
    ; F₁ = _†

    ; identity     = sym identity
    ; homomorphism = λ {_} {_} {_} {f} {g} → homomorphism g f
    ; F-resp-≡     = resp-≡
    }
