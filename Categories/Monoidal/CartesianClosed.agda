module Categories.Monoidal.CartesianClosed where

open import Level

open import Categories.Category

open import Categories.Object.Terminal
open import Categories.Object.Exponential

record CartesianClosed {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  private module C = Category C
  open C hiding (id; identityˡ; identityʳ; assoc)

  field
    terminal : Terminal C
    exponential : ∀ X Y → Exponential C X Y

