module Categories.Rings where

open import Algebra
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_)
import Relation.Binary.EqReasoning as EqR
open import Data.Product

open Σ {{...}}

id+≡0* : ∀ {c ℓ} → (ring : Ring c ℓ)
  → let open Ring ring in
    ∀ {x} → 0# * x ≈ 0#
id+≡0* ring {x} =
  begin
    0# * x
  ≈⟨ sym $ proj₂ +-identity _  ⟩
    0# * x + 0#
  ≈⟨ {!!} ⟩
    0# + 0#
  ≈⟨ proj₁ +-identity 0# ⟩
    0#
  ∎

 where
  open Ring ring
  open EqR (record { isEquivalence = isEquivalence })

id+≡*0 : ∀ {c ℓ} → (ring : Ring c ℓ)
  → let open Ring ring in
    ∀ {x} → x * 0# ≈ 0#
id+≡*0 ring {x} =
  begin
    x * 0#
  ≡⟨ {!!} ⟩
    0#
  ∎

 where
  open Ring ring
  open EqR (record { isEquivalence = isEquivalence })



