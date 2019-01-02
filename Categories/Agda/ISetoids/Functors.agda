module Categories.Agda.ISetoids.Functors {ℓ} where

open import Function.Equality hiding (_∘_)
open import Relation.Binary using (Setoid)
import Relation.Binary.EqReasoning as EqR

open import Categories.Agda
open import Categories.Category
open import Categories.Functor hiding (_≡_) renaming (_∘_ to _∘ᶠ_; id to idᶠ)
open import Categories.Support.PropositionalEquality
open import Categories.Support.EqReasoning


private
  C : Category _ _ _
  C = Setoids ℓ ℓ

  open Category C

≈-cong-app
  : ∀ {f₁ f₂ t₁ t₂} {A : Setoid f₁ f₂} {B : Setoid t₁ t₂}
      {f g : A ⟶ B}
  → (Setoid._≈_ (A ⇨ B) f g)
  → (x : Setoid.Carrier A)
  → (Setoid._≈_ B (f ⟨$⟩ x) (g ⟨$⟩ x))
≈-cong-app f≈g x = {!!}

module ReaderFunctor where
  r→-functor : Obj → Endofunctor C
  r→-functor R = record
    { F₀ = λ A → R ⇨ A
    ; F₁ = λ a⇒b → record
      { _⟨$⟩_ = a⇒b ∘_
      ; cong = F₁-cong a⇒b
      }
    ; identity = {!!}
    ; homomorphism = {!!}
    ; F-resp-≡ = {!!}
    }
    where
    open Relation.Binary using (_=[_]⇒_)
    open Relation.Binary.Setoid
    F₁-cong
      : ∀ {A B}
          (a⇒b : A ⟶ B)
      → _≈_ (R ⇨ A) =[ a⇒b ∘_ ]⇒ _≈_ (R ⇨ B)
    F₁-cong {A} {B} a⇒b {i} {j} i≈j {x} {y} x≈y = let open EqR B in
      begin
        a⇒b ∘ i ⟨$⟩ x
      ≈⟨ cong (a⇒b ∘ i) x≈y ⟩
        a⇒b ∘ i ⟨$⟩ y
      ≡⟨⟩
        a⇒b ⟨$⟩ (i ⟨$⟩ y)
      ≈⟨ cong (a⇒b) (≈-cong-app {A = R} {B = A} {f = i} {g = j} i≈j y) ⟩
        a⇒b ⟨$⟩ (j ⟨$⟩ y)
      ≡⟨⟩
        a⇒b ∘ j ⟨$⟩ y
      ∎

-- Goal: (.B ≈ a⇒b ∘ .i ⟨$⟩ .x) (a⇒b ∘ .j ⟨$⟩ .y)
    {-
    : ∀ {ℓ} {R A B : .Relation.Binary.Setoid ℓ ℓ}
            {a⇒b : Π A (.Relation.Binary.Setoid.indexedSetoid B)}
            {i j : Π R (.Relation.Binary.Setoid.indexedSetoid A)} →
          ({x y : .Relation.Binary.Setoid.Carrier R} →
           (R .Relation.Binary.Setoid.≈ x) y →
           (A .Relation.Binary.Setoid.≈ i ⟨$⟩ x) (j ⟨$⟩ y)) →
          {x y : .Relation.Binary.Setoid.Carrier R} →
          (R .Relation.Binary.Setoid.≈ x) y →
          (B .Relation.Binary.Setoid.≈ a⇒b ⟨$⟩ (i ⟨$⟩ x)) (a⇒b ⟨$⟩ (j ⟨$⟩ y))
          -}

