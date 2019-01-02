module Categories.Agda.Thin where

open import Level
open import Data.Unit
open import Categories.Category
open import Categories.Object.Initial
open import Categories.Object.Terminal
open import Categories.Object.BinaryProducts
open import Relation.Binary
open import Relation.Binary.Lattice
open import Function using (flip; _∘_; _$_)

-- Thin categories

IsThinCategory : ∀ {o ℓ e}
               → (Category o ℓ e)
               → Set _
IsThinCategory C =
  ∀ (A B : Category.Obj C)
    (rel₁ : C [ A , B ])
    (rel₂ : C [ A , B ])
  → C [ rel₁ ≡ rel₂ ]

record ThinCategory o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
    C : Category o ℓ e
    .{is-thin} : IsThinCategory C

private
  thin-eq : ∀ {ℓ} {A : Set ℓ} → Rel A _
  thin-eq = λ _ _ → ⊤

-- Categories from preorders

PreorderCategory : ∀ {c ℓ₁ ℓ₂} → Preorder c ℓ₁ ℓ₂ → Category _ _ _
PreorderCategory preord = record
  { Obj = Carrier
  ; _⇒_ = _∼_
  ; _≡_ = thin-eq

  ; id = refl
  ; _∘_ = flip trans

  ; assoc     = tt
  ; identityˡ = tt
  ; identityʳ = tt
  ; equiv     = record { refl = tt ; sym = λ x → tt ; trans = λ x x₁ → tt }
  ; ∘-resp-≡  = λ x x₁ → tt
  }
  where open Preorder preord

Preorder-IsThin : ∀ {c ℓ₁ ℓ₂} (preord : Preorder c ℓ₁ ℓ₂)
                → IsThinCategory (PreorderCategory preord)
Preorder-IsThin = λ _ _ _ _ _ → tt

PreorderThinCategory : ∀ {c ℓ₁ ℓ₂} → Preorder c ℓ₁ ℓ₂ → ThinCategory _ _ _
PreorderThinCategory preord = record { C = PreorderCategory preord }

-- Categories from join semilattices

JoinSemilatticeCategory : ∀ {a ℓ₁ ℓ₂} → JoinSemilattice a ℓ₁ ℓ₂ → Category _ _ _
JoinSemilatticeCategory = PreorderCategory ∘ JoinSemilattice.preorder

BoundedJoinSemilatticeCategory : ∀ {a ℓ₁ ℓ₂} → BoundedJoinSemilattice a ℓ₁ ℓ₂ → Category _ _ _
BoundedJoinSemilatticeCategory = PreorderCategory ∘ BoundedJoinSemilattice.preorder

BoundedJoinSemilattice-Initial
  : ∀ {a ℓ₁ ℓ₂}
  → (bjsl : BoundedJoinSemilattice a ℓ₁ ℓ₂)
  → Initial (BoundedJoinSemilatticeCategory bjsl)
BoundedJoinSemilattice-Initial bjsl = record
    { ⊥ = ⊥
    ; ! = λ {X} → minimum X
    ; !-unique = λ _ → tt
    }
  where open BoundedJoinSemilattice bjsl

MeetSemilatticeCategory : ∀ {a ℓ₁ ℓ₂} → MeetSemilattice a ℓ₁ ℓ₂ → Category _ _ _
MeetSemilatticeCategory = PreorderCategory ∘ MeetSemilattice.preorder

BoundedMeetSemilatticeCategory : ∀ {a ℓ₁ ℓ₂} → BoundedMeetSemilattice a ℓ₁ ℓ₂ → Category _ _ _
BoundedMeetSemilatticeCategory = PreorderCategory ∘ BoundedMeetSemilattice.preorder

BoundedMeetSemilattice-Terminal
  : ∀ {a ℓ₁ ℓ₂}
  → (bmsl : BoundedMeetSemilattice a ℓ₁ ℓ₂)
  → Terminal (BoundedMeetSemilatticeCategory bmsl)
BoundedMeetSemilattice-Terminal bmsl = record
  { ⊤ = bmsl.⊤
  ; ! = λ {X} → bmsl.maximum X
  ; !-unique = λ _ → tt
  }
 where module bmsl = BoundedMeetSemilattice bmsl


  -- coproducts : Coproducts
  -- coproducts = record
  --   { initial = initial
  --   ; binary = record
  --     { coproduct = λ {A B} → record
  --       { A+B = _
  --       ; i₁ = {!!}
  --       ; i₂ = {!!}
  --       ; [_,_] = {!!}
  --       ; commute₁ = {!!}
  --       ; commute₂ = {!!}
  --       ; universal = {!!}
  --       }
  --     }
  --   }
