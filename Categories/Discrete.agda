{-# OPTIONS --universe-polymorphism #-}
module Categories.Discrete where

open import Level
open import Data.Unit using (⊤)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Function using (flip; _∘_)

open import Categories.Category
open import Categories.Support.PropositionalEquality

Discrete : ∀ {o} (A : Set o) → Category o o zero
Discrete A = record
  { Obj = A
  ; _⇒_ = _≣_
  ; _≡_ = λ _ _ → ⊤
  ; _∘_ = flip ≣-trans
  ; id = ≣-refl
  }

Discreteₙ : ℕ → Category zero zero zero
Discreteₙ = Discrete ∘ Fin
