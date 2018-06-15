{-# OPTIONS --universe-polymorphism #-}
module Categories.Monad where

open import Level

open import Categories.Category
open import Categories.Functor hiding (_≡_; assoc; identityˡ; identityʳ)
open import Categories.NaturalTransformation renaming (id to idN)

record Monad {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  field
    F : Endofunctor C
    η : NaturalTransformation id F
    μ : NaturalTransformation (F ∘ F) F

  open Functor  F

  field
    .assoc     : μ ∘₁ (F ∘ˡ μ) ≡ μ ∘₁ (μ ∘ʳ F)
    .identityˡ : μ ∘₁ (F ∘ˡ η) ≡ idN
    .identityʳ : μ ∘₁ (η ∘ʳ F) ≡ idN

  return : ∀ {A} → C [ A , F ⟨ A ⟩ ]
  return = η.η _
    where module η = NaturalTransformation η

  join : ∀ {A} → C [ F ⟨ F ⟨ A ⟩ ⟩ , F ⟨ A ⟩ ]
  join = μ.η _
    where module μ = NaturalTransformation μ

  bind : ∀ {A B} → C [ A , F₀ B ] → C [ F ⟨ A ⟩ , F ⟨ B ⟩ ]
  bind f = C [ join ∘ F₁ f ]

