{-# OPTIONS --universe-polymorphism #-}

module Categories.Agda.Preorder where

open import Relation.Binary using (Rel; Preorder; IsPreorder)
open import Categories.Category
open import Function using (flip; _∋_)
open import Data.Unit
open import Data.Product using (_×_; ∃; _,′_; swap; Σ)
open import Level using (zero; suc; _⊔_)

record IPreorder c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    Carrier : Set c
    _≈_ : Rel Carrier ℓ₁ -- Equality relationship
    _∼_ : Rel Carrier ℓ₂ -- Equality relationship
    .isPreorder : IsPreorder _≈_ _∼_

Preorder→IPreorder : ∀ {c ℓ₁ ℓ₂}
                   → Preorder c ℓ₁ ℓ₂
                   → IPreorder c ℓ₁ ℓ₂
Preorder→IPreorder p = record
  { Carrier = P.Carrier
  ; _≈_ = P._≈_
  ; _∼_ = P._∼_
  ; isPreorder = P.isPreorder
  }
 where module P = Preorder p


IsThinCategory : ∀ {o ℓ e} → (Category o ℓ e) → Set _
IsThinCategory C = ∀ {A B} → ∀ (rel₁ : C [ A , B ])
                               (rel₂ : C [ A , B ])
                           → C [ rel₁ ≡ rel₂ ]

PreorderCategory : ∀ {a ℓ₁ ℓ₂} → Preorder a ℓ₁ ℓ₂ → Category a ℓ₂ zero
PreorderCategory preord = record
  { Obj = Carrier
  ; _⇒_ = _∼_
  -- As there's only one morphism between any two objects, all parallel
  -- morhpisms in a preorder category can be considered equal
  ; _≡_ = λ _ _ → ⊤

  ; _∘_ = flip trans
  ; id  = refl

  ; assoc = tt
  ; identityˡ = tt
  ; identityʳ = tt
  ; equiv = record { refl = tt ; sym = λ _ → tt; trans = λ _ _ → tt }
  ; ∘-resp-≡ = λ _ _ → tt
  }
  where open Preorder preord

thinPreorder : ∀ {a ℓ₁ ℓ₂} (preord : Preorder a ℓ₁ ℓ₂)
             → (IsThinCategory (PreorderCategory preord))
thinPreorder _ _ _ = tt

Category→IPreorder : ∀ {o ℓ e} (C : Category o ℓ e) → IPreorder _ _ _
Category→IPreorder C = record
  { Carrier    = Obj
  ; _≈_        = λ A B → (A ⇒ B × B ⇒ A)
  ; _∼_        = _⇒_
  ; isPreorder = record
    { isEquivalence = record
      { refl = λ {x} → id ,′ id
      ; sym = swap
      ; trans = trans
      }
    ; reflexive = Σ.proj₁
    ; trans = flip _∘_
    }
  }
 where
  open Category C
  trans : Relation.Binary.Transitive (λ A B → (A ⇒ B × B ⇒ A))
  -- NOTE could use profunctor.dimap?
  trans (i≤j Σ., j≤i) (j≤k Σ., k≤j) = j≤k ∘ i≤j ,′ j≤i ∘ k≤j
