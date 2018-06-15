{-# OPTIONS --allow-unsolved-metas #-}

module Categories.Agda.ISetoids.CartesianClosed where

open import Level

open import Data.Unit renaming (setoid to ⊤-setoid)
open import Data.Product

open import Categories.Category
open import Categories.Agda
open import Categories.Agda.ISetoids.Objects
open import Categories.Agda.ISetoids.Products
open import Categories.Object.BinaryProducts
open import Categories.Object.Products
open import Categories.Monoidal.CartesianClosed
open import Categories.Support.SetoidFunctions
open import Categories.Support.PropositionalEquality
open import Categories.Bifunctor using (_⟨_,_⟩)
open import Categories.Functor.Hom

C : Category _ _ _
C = ISetoids zero zero

module C = Category C

ISetoidsCartesianClosed : CartesianClosed C
ISetoidsCartesianClosed = record
  { terminal = terminal
  ; exponential = λ X Y → record
    { B^A = Hom[ C ][-,-] ⟨ X , Y ⟩
    ; product = BinaryProducts.product ∘ Products.binary $ products
    ; eval = eval
    ; λg = {!!}
    ; β = {!!}
    ; λ-unique = {!!}
    }
  }
 where
   open import Function
   open C using (_⇒_)
   eval : ∀ {X Y} → (Hom[ C ][-,-] ⟨ X , Y ⟩) ×′ X ⇒ Y
   eval = record { _⟨$⟩_ = λ { (xy , x) → xy ⟨$⟩ x } ; cong = λ { (xy , x) → {!!} } }
      {-
      record
      { Carrier = A ⟶ B
      ; _≈_ = λ f g → ∀ x → f ⟨$⟩ x ≣ g ⟨$⟩ x
      ; isEquivalence = record
        { refl = λ x₁ → ≣-refl
        ; sym = λ x x₁ → {!!}
        ; trans = {!!}
        }
      }
      -}
