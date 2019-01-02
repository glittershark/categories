{-# OPTIONS --universe-polymorphism #-}
module Categories.Monad where

open import Level
open import Function hiding (id; _∘_)

open import Data.Product

open import Categories.Category
open import Categories.Object.Monoid
open import Categories.Functor hiding (assoc; identityˡ; identityʳ) renaming (_≡_ to _≡ᶠ_)
open import Categories.FunctorCategory
open import Categories.NaturalTransformation renaming (id to idN; _≡_ to _≡ⁿ_)

record Monad {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  field
    F : Endofunctor C
    η : NaturalTransformation id F
    μ : NaturalTransformation (F ∘ F) F

  open Functor F

  field
    .assoc     : μ ∘₁ (F ∘ˡ μ) ≡ⁿ μ ∘₁ (μ ∘ʳ F)
    .identityˡ : μ ∘₁ (F ∘ˡ η) ≡ⁿ idN
    .identityʳ : μ ∘₁ (η ∘ʳ F) ≡ⁿ idN

return : ∀ {o ℓ e} {C : Category o ℓ e} {A : Category.Obj C} {M : Monad C}
       → C [ A ⇒ (Monad.F M) ⟨ A ⟩₀ ]
return {A = A} {M = M} = NaturalTransformation.η (Monad.η M) A

return[_] : ∀ {o ℓ e} {C : Category o ℓ e} {A : Category.Obj C} (M : Monad C)
          → C [ A ⇒ (Monad.F M) ⟨ A ⟩₀ ]
return[ M ] = return {M = M}

join : ∀ {o ℓ e} {C : Category o ℓ e} {A : Category.Obj C} {M : Monad C}
     → C [ (Monad.F M ∘ Monad.F M) ⟨ A ⟩₀ ⇒ (Monad.F M) ⟨ A ⟩₀ ]
join {A = A} {M = M} = NaturalTransformation.η (Monad.μ M) A

join[_] : ∀ {o ℓ e} {C : Category o ℓ e} {A : Category.Obj C} (M : Monad C)
     → C [ (Monad.F M ∘ Monad.F M) ⟨ A ⟩₀ ⇒ (Monad.F M) ⟨ A ⟩₀ ]
join[ M ] = join {M = M}


Monads : ∀ {o ℓ e} → Category o ℓ e → Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) (o ⊔ e)
Monads Cat = record
  { Obj = Monad Cat
  ; _⇒_ = NaturalTransformation on F
  ; _≡_ = Func._≡_
  ; _∘_ = Func._∘_
  ; id  = Func.id

  ; assoc = λ {A} {B} {C} {D} {f} {g} {h} → Func.assoc {F A} {F B} {F C} {F D} {f} {g} {h}
  ; identityˡ = λ {A} {B} {f} → Func.identityˡ {F A} {F B} {f}
  ; identityʳ = λ {A} {B} {f} → Func.identityʳ {F A} {F B} {f}
  ; equiv = λ {A} {B} → Func.equiv {F A} {F B}
  ; ∘-resp-≡ = λ {A} {B} {C} {f} {g} {h} {i} → Func.∘-resp-≡ {F A} {F B} {F C} {f} {g} {h} {i}
  }
 where
  open Monad using (F)
  module Func = Category (Functors Cat Cat)

MonadTransformer : ∀ {o ℓ e} → Category o ℓ e → Set (o ⊔ ℓ ⊔ e)
MonadTransformer C = Monad (Monads C)

-- ----------------------------------------------------------------------------

-- monad-monoid-endofunctors : ∀ {o ℓ e} {C : Category o ℓ e} (M : Monad C) → Monoid (Endofunctors C) (Monad.F M)
-- monad-monoid-endofunctors M = record
--   { ⊤ = id
--   ; A² = F ∘ F
--   ; _×_ = {!!}
--   ; mempty = η
--   ; mappend = μ
--   ; identityˡ = {!!}
--   ; identityʳ = {!!}
--   ; assoc = {!assoc!}
--   }
--  where
--    open Monad M

-- -- Goal: (x y z : id ⇒ F)
-- --     →
-- --       (μ ∘₁ (?0 M x (μ ∘₁ (?0 M y z)))
-- --        ≡
-- --       ((Endofunctors .C Category.∘ μ)
-- --        (?0 M ((Endofunctors .C Category.∘ μ) (?0 M x y)) z))

