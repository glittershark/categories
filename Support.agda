{-# OPTIONS --universe-polymorphism #-}

-- Support stuff mostly stolen or adapted from the Agda standard library

module Support where

data Level : Set where
  zero : Level
  suc  : (i : Level) → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}

-- Maximum.

infixl 6 _⊔_
infixr 2 _×_

_⊔_ : Level → Level → Level
zero  ⊔ j     = j
suc i ⊔ zero  = suc i
suc i ⊔ suc j = suc (i ⊔ j)

{-# BUILTIN LEVELMAX _⊔_ #-}

infixr 4 _,_

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

∃ : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃ = Σ _

∃₂ : ∀ {a b c} {A : Set a} {B : A → Set b}
     (C : (x : A) → B x → Set c) → Set (a ⊔ b ⊔ c)
∃₂ C = ∃ λ a → ∃ λ b → C a b


record Σ′ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    proj′₁ : A
    .proj′₂ : B proj′₁

open Σ′ public

∃′ : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃′ = Σ′ _

∃₂′ : ∀ {a b c} {A : Set a} {B : A → Set b}
     (C : (x : A) → B x → Set c) → Set (a ⊔ b ⊔ c)
∃₂′ C = ∃ λ a → ∃′ λ b → C a b

record _×_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B

open _×_ public

_∙_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f ∙ g = λ x → f (g x)

_∙′_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
       (B → C) → (A → B) → (A → C)
f ∙′ g = _∙_ f g

flip : ∀ {a b c} {A : Set a} {B : Set b} {C : A → B → Set c} →
       ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip f = λ x y → f y x

Rel : ∀ {a} → Set a → (ℓ : Level) → Set (a ⊔ suc ℓ)
Rel A ℓ = A → A → Set ℓ

_⇒_ : ∀ {a ℓ₁ ℓ₂} {A : Set a} →
      Rel A ℓ₁ → Rel A ℓ₂ → Set _
P ⇒ Q = ∀ {i j} → P i j → Q i j

_Respects_ : ∀ {a ℓ₁ ℓ₂} {A : Set a} → (A → Set ℓ₁) → Rel A ℓ₂ → Set _
P Respects _∼_ = ∀ {x y} → x ∼ y → P x → P y

_Respects₂_ : ∀ {a ℓ₁ ℓ₂} {A : Set a} → Rel A ℓ₁ → Rel A ℓ₂ → Set _
P Respects₂ _∼_ =
  (∀ {x} → P x      Respects _∼_) ×
  (∀ {y} → flip P y Respects _∼_)

record IsEquivalence {a ℓ} {A : Set a}
                     (_≈_ : Rel A ℓ) : Set (a ⊔ ℓ) where
  field
    refl  : ∀ {x} → x ≈ x
    sym   : ∀ {x y} → x ≈ y → y ≈ x
    trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z


record IsPreorder {a ℓ₁ ℓ₂} {A : Set a}
                  (_≈_ : Rel A ℓ₁) -- The underlying equality.
                  (_∼_ : Rel A ℓ₂) -- The relation.
                  : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isEquivalence : IsEquivalence _≈_
    -- Reflexivity is expressed in terms of an underlying equality:
    reflexive     : _≈_ ⇒ _∼_
    trans         : ∀ {x y z} → x ∼ y → y ∼ z → x ∼ z

  module Eq = IsEquivalence isEquivalence

  refl : ∀ {x} → x ∼ x
  refl = reflexive Eq.refl

  ∼-resp-≈ : _∼_ Respects₂ _≈_
  ∼-resp-≈ = (λ x≈y z∼x → trans z∼x (reflexive x≈y))
           , (λ x≈y x∼z → trans (reflexive (Eq.sym x≈y)) x∼z)

record Preorder c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _∼_
  field
    Carrier    : Set c
    _≈_        : Rel Carrier ℓ₁  -- The underlying equality.
    _∼_        : Rel Carrier ℓ₂  -- The relation.
    isPreorder : IsPreorder _≈_ _∼_

  open IsPreorder isPreorder public


record Setoid c ℓ : Set (suc (c ⊔ ℓ)) where
  infix 4 _≈_
  field
    Carrier       : Set c
    _≈_           : Rel Carrier ℓ
    .isEquivalence : IsEquivalence _≈_




module SetoidReasoning {s₁ s₂} (S : Setoid s₁ s₂) where
  open Setoid S

  infix  4 _IsRelatedTo_
  infix  2 _∎
  infixr 2 _≈⟨_⟩_
  infix  1 begin_

  -- This seemingly unnecessary type is used to make it possible to
  -- infer arguments even if the underlying equality evaluates.

  data _IsRelatedTo_ (x y : Carrier) : Set s₂ where
    relTo : (x∼y : x ≈ y) → x IsRelatedTo y

  .begin_ : ∀ {x y} → x IsRelatedTo y → x ≈ y
  begin relTo x∼y = x∼y

  ._≈⟨_⟩_ : ∀ x {y z} → x ≈ y → y IsRelatedTo z → x IsRelatedTo z
  _ ≈⟨ x∼y ⟩ relTo y∼z = relTo (trans x∼y y∼z)
    where open IsEquivalence isEquivalence

  ._∎ : ∀ x → x IsRelatedTo x
  _∎ _ = relTo refl
    where open IsEquivalence isEquivalence

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}

data Fin : ℕ → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} → Fin n → Fin (suc n)