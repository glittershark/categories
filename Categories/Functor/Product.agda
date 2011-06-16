{-# OPTIONS --universe-polymorphism #-}
module Categories.Functor.Product where

open import Categories.Category
open import Categories.Functor using (Functor)
import Categories.Object.Product as Product
import Categories.Object.BinaryProducts as BinaryProducts

-- Ugh, we should start bundling things (categories with binary products, in this case) up consistently
_[_][_×-] : ∀ {o ℓ e} → (C : Category o ℓ e) → BinaryProducts.BinaryProducts C → Category.Obj C → Functor C C
C [ P ][ O ×-] = record 
  { F₀ = λ x → Product.A×B (product {O} {x})
  ; F₁ = λ f → ⟨ π₁ , f ∘ π₂ ⟩
  ; identity = λ {x} → identity′ {x}
  ; homomorphism = λ {x} {y} {z} {f} {g} → homomorphism′ {x} {y} {z} {f} {g}
  ; F-resp-≡ = λ f≡g → ⟨⟩-cong₂ refl (∘-resp-≡ˡ f≡g)
  }
  where
  open Category C
  open Equiv
  open Product C
  open BinaryProducts.BinaryProducts C P

  .identity′ : {A : Obj} → ⟨ π₁ , id ∘ π₂ ⟩ ≡ id
  identity′ = 
    begin
      ⟨ π₁ , id ∘ π₂ ⟩
    ≈⟨ ⟨⟩-cong₂ refl identityˡ ⟩
      ⟨ π₁ , π₂ ⟩
    ≈⟨ η ⟩
      id
    ∎
    where open HomReasoning

  .homomorphism′ : {X Y Z : Obj} {f : X ⇒ Y} {g : Y ⇒ Z} → ⟨ π₁ , (g ∘ f) ∘ π₂ ⟩ ≡ ⟨ π₁ , g ∘ π₂ ⟩ ∘ ⟨ π₁ , f ∘ π₂ ⟩ 
  homomorphism′ {f = f} {g} =
    begin
      ⟨ π₁ , (g ∘ f) ∘ π₂ ⟩
    ↓⟨ ⟨⟩-cong₂ refl assoc ⟩
      ⟨ π₁ , g ∘ (f ∘ π₂) ⟩
    ↑⟨ ⟨⟩-cong₂ refl (∘-resp-≡ʳ commute₂) ⟩
      ⟨ π₁ , g ∘ (π₂ ∘ ⟨ π₁ , f ∘ π₂ ⟩) ⟩
    ↑⟨ ⟨⟩-cong₂ commute₁ assoc ⟩
       ⟨ π₁ ∘ ⟨ π₁ , f ∘ π₂ ⟩  , (g ∘ π₂) ∘ ⟨ π₁ , f ∘ π₂ ⟩ ⟩
    ↑⟨ ⟨⟩∘ ⟩
      ⟨ π₁ , g ∘ π₂ ⟩ ∘ ⟨ π₁ , f ∘ π₂ ⟩ 
    ∎
    where open HomReasoning
