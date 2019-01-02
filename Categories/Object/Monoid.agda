open import Categories.Category
open import Categories.Object.Terminal

module Categories.Object.Monoid {o ℓ e} (C : Category o ℓ e) where

open Category C

open import Level
open import Categories.Object.Product C

record Monoid (A : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    ⊤  : Obj

  private
    A′ = ⊤ ⇒ A

  field
    A² : Obj

  private
    A²′ = ⊤ ⇒ A²

  field
    _×_ : A′ → A′ → ⊤ ⇒ A²

    mempty  : A′
    mappend : A² ⇒ A

  _∙_ : A′ → A′ → A′
  f ∙ g = mappend ∘ f × g

  field
    .identityˡ : ∀ x → mempty ∙ x ≡ x
    .identityʳ : ∀ x → x ∙ mempty ≡ x
    .assoc : ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z

-- Monoid′ : (A : Obj) ⦃ t : Terminal C ⦄ ⦃ p : Product A A ⦄ → Set (o ⊔ ℓ ⊔ e)
-- Monoid′ = {!!}
  -- field
  --   ⦃ t ⦄ : Terminal C
  --   ⦃ p ⦄ : Product A A

  -- open Terminal t
  -- open Product p

  -- private
  --   A′ = ⊤ ⇒ A

  -- field
  --   mempty  : A′
  --   mappend : C [ A×B ⇒ A ]

  -- _∙_ : A′ → A′ → A′
  -- f ∙ g = mappend ∘ ⟨ f , g ⟩

  -- field
  --   identityˡ : ∀ x → mempty ∙ x ≡ x
  --   identityʳ : ∀ x → x ∙ mempty ≡ x
  --   assoc : ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z
