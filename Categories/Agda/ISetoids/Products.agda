{-# OPTIONS --universe-polymorphism #-}
{-# OPTIONS --allow-unsolved-metas #-}

module Categories.Agda.ISetoids.Products where

open import Level using (zero)

open import Categories.Agda
open import Categories.Object.Products
open import Categories.Support.PropositionalEquality
open import Categories.Support.Equivalence
open import Categories.Support.SetoidFunctions
open import Relation.Binary using (Rel)
open import Data.Unit renaming (setoid to ⊤-setoid)
open import Data.Product
open import Function

infix 30 _×′_

_×′_ : Setoid zero zero → Setoid zero zero → Setoid zero zero
A ×′ B = record
  { Carrier = T
  ; _≈_ = _≈_
  ; isEquivalence = record
    { refl = reflᴬ , reflᴮ
    ; sym = λ x → {!!} , {!!}
    ; trans = λ x x₁ → {!!} , {!!}
    }
  }
 where
  Aᵀ = Setoid.Carrier A
  Bᵀ = Setoid.Carrier B
  T = Aᵀ × Bᵀ

  _≈ᴬ_ = Setoid._≈_ A
  _≈ᴮ_ = Setoid._≈_ B

  _≈_ : Rel T zero
  (A₁ , B₁) ≈ (A₂ , B₂) = A₁ ≈ᴬ A₂ × B₁ ≈ᴮ B₂

  .reflᴬ : {!!}
  reflᴬ  = Setoid.refl A
  .reflᴮ : {!!}
  reflᴮ  = Setoid.refl B
  .symᴬ : {!!}
  symᴬ   = Setoid.sym A
  .symᴮ : {!!}
  symᴮ   = Setoid.sym B
  .transᴬ : {!!}
  transᴬ = Setoid.trans A
  .transᴮ : {!!}
  transᴮ = Setoid.trans B

products : Products (ISetoids zero zero)
products = record
  { terminal = record
    { ⊤ = record { Carrier = ⊤ ; _≈_ = _≣_ ; isEquivalence = ≣-isEquivalence }
    ; ! = record { _⟨$⟩_ = λ x → tt ; cong = λ x → ≣-refl }
    ; !-unique = λ _ _ → ≣-refl
    }
  ; binary = record
    { product = λ {A B} → record
      { A×B = A ×′ B
      ; π₁ = record { _⟨$⟩_ = proj₁ ; cong = {!!} }
      ; π₂ = record { _⟨$⟩_ = proj₂ ; cong = {!!} }
      ; ⟨_,_⟩ = λ fᴬ fᴮ → record { _⟨$⟩_ = λ c → fᴬ ⟨$⟩ c , fᴮ ⟨$⟩ c ; cong = {!!} }
      ; commute₁ = {!!}
      ; commute₂ = {!!}
      ; universal = {!!}
      }
    }
  }
