module Categories.Agda.ISetoids.Objects where

open import Level
open import Categories.Agda
open import Categories.Object.Terminal
open import Categories.Object.Initial
open import Data.Unit
open import Data.Empty

initial : Initial (ISetoids zero zero)
initial = record
  { ⊥ = record
    { Carrier = ⊥
    ; _≈_ = λ _ _ → ⊥
    ; isEquivalence = record
      { refl = λ {x} → ⊥-elim x ; sym = ⊥-elim ; trans = λ _ → ⊥-elim }
    }
  ; ! = record { _⟨$⟩_ = λ () ; cong = ⊥-elim }
  ; !-unique = λ f ()
  }

terminal : Terminal (ISetoids zero zero)
terminal = record
  { ⊤ = record
    { Carrier = ⊤
    ; _≈_ = λ x x₁ → ⊤
    ; isEquivalence = record
      { refl = tt ; sym = λ _ → tt ; trans = λ _ _ → tt }
    }
  ; ! = record { _⟨$⟩_ = λ _ → tt ; cong = λ _ → tt }
  ; !-unique = λ _ _ → tt
  }
