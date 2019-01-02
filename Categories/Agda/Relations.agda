module Categories.Agda.Relations where

open import Level
open import Function
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality using (_≗_)
open import Relation.Binary.HeterogeneousEquality as HetEq using (_≅_)
open import Data.Product hiding (,_)
open import Data.Unit
import Relation.Binary.Simple
import Relation.Binary.EqReasoning as EqReasoning

open import Categories.Agda
open import Categories.Category
import Categories.Support.Equivalence
import Categories.Support.SetoidFunctions
open import Categories.Support.PropositionalEquality
open import Categories.Functor using (Functor)
open import Categories.Dagger

_∘ᴿ_ : ∀ {ℓ} {X Y Z : Set ℓ} → REL Y Z ℓ → REL X Y ℓ → REL X Z ℓ
rel₁ ∘ᴿ rel₂ = λ x z → ∃ λ y → rel₁ y z × rel₂ x y

record _≡ᴿ_ {ℓ} {X Y : Set ℓ} (f : REL X Y ℓ) (g : REL X Y ℓ) : Set ℓ where
  field
    hither : ∀ x y → f x y → g x y
    yon    : ∀ x y → g x y → f x y

    .cancel⃗ : ∀ x y → hither x y ∘ yon x y ≗ id
    .cancel⃖ : ∀ x y → yon x y ∘ hither x y ≗ id

≡ᴿ-refl : ∀ {ℓ} {X Y : Set ℓ} {f : REL X Y ℓ} → f ≡ᴿ f
≡ᴿ-refl = record
  { hither = λ _ _ z → z
  ; yon = λ _ _ z → z
  ; cancel⃗ = λ _ _ _ → ≣-refl
  ; cancel⃖ = λ _ _ _ → ≣-refl
  }

≣-to-≡ᴿ : ∀ {ℓ} {X Y : Set ℓ} (f g : REL X Y ℓ) → f ≣ g → f ≡ᴿ g
≣-to-≡ᴿ f .f ≣-refl = ≡ᴿ-refl

≡ᴿ-sym : ∀ {ℓ} {X Y : Set ℓ} {f g : REL X Y ℓ} → f ≡ᴿ g → g ≡ᴿ f
≡ᴿ-sym record { hither = hither ; yon = yon ; cancel⃗ = cancel⃗ ; cancel⃖ = cancel⃖ }
  = record { hither = yon ; yon = hither ; cancel⃗ = cancel⃖ ; cancel⃖ = cancel⃗ }

≡ᴿ-trans : ∀ {ℓ} {X Y : Set ℓ} {f g h : REL X Y ℓ} → f ≡ᴿ g → g ≡ᴿ h → f ≡ᴿ h
≡ᴿ-trans {ℓ} {f=f} {g=g} {h=h} f≡ᴿg g≡ᴿh = record
  { hither  = λ x y → hither₂ x y ∘ hither₁ x y
  ; yon     = λ x y → yon₁ x y    ∘ yon₂ x y
  ; cancel⃗ = λ x y hxy → let open ≣-reasoning in
    begin
      (hither₂ x y ∘ (hither₁ x y ∘ yon₁ x y) ∘ yon₂ x y) hxy
    ≣⟨ ≣-cong (hither₂ x y) ∘ cancel⃗₁ x y $ yon₂ x y hxy ⟩
      (hither₂ x y ∘ yon₂ x y) hxy
    ≣⟨ cancel⃗₂ x y hxy ⟩
      hxy
    ∎
  ; cancel⃖ = λ x y hxy → let open ≣-reasoning in
    begin
      (yon₁ x y ∘ yon₂ x y ∘ hither₂ x y ∘ hither₁ x y) hxy
    ≣⟨ ≣-cong (yon₁ x y) ∘ cancel⃖₂ x y $ hither₁ x y hxy ⟩
      (yon₁ x y ∘ hither₁ x y) hxy
    ≣⟨ cancel⃖₁ x y hxy ⟩
      hxy
    ∎

  }
  where
    open _≡ᴿ_ f≡ᴿg
      renaming ( hither to hither₁
               ; yon to yon₁
               ; cancel⃗ to cancel⃗₁
               ; cancel⃖ to cancel⃖₁
               )
    open _≡ᴿ_ g≡ᴿh
      renaming ( hither to hither₂
               ; yon to yon₂
               ; cancel⃗ to cancel⃗₂
               ; cancel⃖ to cancel⃖₂
               )


Relations : ∀ ℓ → Category _ _ _
Relations ℓ = record
  { Obj = Set ℓ
  ; _⇒_ = λ x y → REL x y ℓ
  ; _≡_ = _≡ᴿ_

  ; _∘_ = _∘ᴿ_
  ; id = _≣_

  ; assoc = record
    { hither = assoc⃗
    ; yon = assoc⃖
    ; cancel⃖ = λ _ _ _ → ≣-refl
    ; cancel⃗ = λ _ _ _ → ≣-refl
    }
  ; identityˡ = record
    { hither = identityˡ⃗
    ; yon = identityˡ⃖
    ; cancel⃗ = λ _ _ _ → ≣-refl
    ; cancel⃖ = λ { _ _ (_ , ≣-refl , _) → ≣-refl }
    }
  ; identityʳ = record
    { hither = identityʳ⃗
    ; yon =  identityʳ⃖
    ; cancel⃗ = λ _ _ _ → ≣-refl
    ; cancel⃖ = λ { _ _ (_ , _ , ≣-refl) → ≣-refl }
    }
  ; equiv = record
    { refl = ≡ᴿ-refl
    ; sym = ≡ᴿ-sym
    ; trans = ≡ᴿ-trans
    }
  ; ∘-resp-≡ = ∘-resp-≣
  }
 where
  open Relation.Binary.Simple using (Always)

  assoc⃗
    : ∀ {A B C D : Set ℓ}
        {f : REL A B ℓ}
        {g : REL B C ℓ}
        {h : REL C D ℓ}
        (x : A)
        (y : D)
    → Σ[ z ∈ B ] Σ[ x₁ ∈ Σ[ y₂ ∈ C ] Σ[ x₁ ∈ h y₂ y ] g z y₂ ] f x z
    → Σ[ z ∈ C ] Σ[ x₁ ∈ h z y ] Σ[ y₂ ∈ B ] Σ[ x₂ ∈ g y₂ z ] f x y₂
  assoc⃗ x y (b , (c , hcy , gbc) , fxb) = c , hcy , b , gbc , fxb

  assoc⃖
    : ∀ {A B C D : Set ℓ}
        {f : REL A B ℓ}
        {g : REL B C ℓ}
        {h : REL C D ℓ}
        (x : A)
        (y : D)
    → Σ[ z ∈ C ] Σ[ x₁ ∈ h z y ] Σ[ y₂ ∈ B ] Σ[ x₂ ∈ g y₂ z ] f x y₂
    → Σ[ z ∈ B ] Σ[ x₁ ∈ Σ[ y₂ ∈ C ] Σ[ x₁ ∈ h y₂ y ] g z y₂ ] f x z
  assoc⃖ x y (c , hcy , b , gbc , fxb) = b , (c , hcy , gbc) , fxb

  identityˡ⃗
    : ∀ {A B : Set ℓ}
        {f : REL A B ℓ}
        (x : A)
        (y : B)
    → Σ[ b ∈ B ] Σ[ _ ∈ b ≣ y ] f x b
    → f x y
  identityˡ⃗ _ y (.y , ≣-refl , fxy) = fxy

  identityˡ⃖
    : ∀ {A B : Set ℓ}
        {f : REL A B ℓ}
        (x : A)
        (y : B)
    → f x y
    → Σ[ b ∈ B ] Σ[ _ ∈ b ≣ y ] f x b
  identityˡ⃖ x y z = y , ≣-refl , z

  identityʳ⃗
    : ∀ {A B : Set ℓ}
        {f : REL A B ℓ}
        (x : A)
        (y : B)
    → Σ[ a ∈ A ] Σ[ _ ∈ f a y ] x ≣ a
    → f x y
  identityʳ⃗ x y (.x , fxy , ≣-refl) = fxy

  identityʳ⃖
    : ∀ {A B : Set ℓ}
        {f : REL A B ℓ}
        (x : A)
        (y : B)
    → f x y
    → Σ[ a ∈ A ] Σ[ _ ∈ f a y ] x ≣ a
  identityʳ⃖ x y fxy = x , fxy , ≣-refl

  ∘-resp-≣
    : ∀ {A B C : Set ℓ}
        {f h : REL B C ℓ}
        {g i : REL A B ℓ}
    → f ≡ᴿ h
    → g ≡ᴿ i
    → (f ∘ᴿ g) ≡ᴿ (h ∘ᴿ i)
  ∘-resp-≣ {A} {B} {C} {f} {h} {g} {i} f≡ᴿh g≡ᴿi = record
      { hither = hither
      ; yon = yon
      ; cancel⃗ = cancel⃗
      ; cancel⃖ = cancel⃖
      }
    where
      open _≡ᴿ_ f≡ᴿh
        renaming ( hither to hither₁
                 ; yon to yon₁
                 ; cancel⃗ to cancel⃗₁
                 ; cancel⃖ to cancel⃖₁
                 )
      open _≡ᴿ_ g≡ᴿi
        renaming ( hither to hither₂
                 ; yon to yon₂
                 ; cancel⃗ to cancel⃗₂
                 ; cancel⃖ to cancel⃖₂
                 )

      hither : ∀ (x : A) (y : C) → (f ∘ᴿ g) x y → (h ∘ᴿ i) x y
      hither x y (b , fly , gxl ) = b , hither₁ b y fly , hither₂ x b gxl
      yon : ∀ (x : A) (y : C) → (h ∘ᴿ i) x y → (f ∘ᴿ g) x y
      yon x y (b , hby , ixb) = b , yon₁ b y hby , yon₂ x b ixb

      .cancel⃗ : ∀ (x : A) (y : C) → hither x y ∘ yon x y ≗ id
      cancel⃗ x y z@(b , hby , ixb) = let open ≣-reasoning in
        begin
          (hither x y ∘ yon x y) z
        ≣⟨⟩
          hither x y (b , yon₁ b y hby , yon₂ x b ixb)
        ≣⟨⟩
          b , hither₁ b y (yon₁ b y hby) , hither₂ x b (yon₂ x b ixb)
        ≣⟨ ≣-cong (λ xx → b , xx , hither₂ x b (yon₂ x b ixb)) (cancel⃗₁ b y hby ) ⟩
          b , hby , hither₂ x b (yon₂ x b ixb)
        ≣⟨ ≣-cong (λ xx → b , hby , xx) (cancel⃗₂ x b ixb) ⟩
          b , hby , ixb
        ≣⟨⟩
         z
        ∎

      .cancel⃖ : ∀ (x : A) (y : C) → yon x y ∘ hither x y ≗ id
      cancel⃖ x y z@(b , fby , gxb) = let open ≣-reasoning in
        begin
          (yon x y ∘ hither x y) z
        ≣⟨⟩
          yon x y (b , hither₁ b y fby , hither₂ x b gxb)
        ≣⟨⟩
          b , yon₁ b y (hither₁ b y fby) , yon₂ x b (hither₂ x b gxb)
        ≣⟨ ≣-cong (λ xx → b , xx , yon₂ x b (hither₂ x b gxb)) (cancel⃖₁ b y fby) ⟩
          b , fby , yon₂ x b (hither₂ x b gxb)
        ≣⟨ ≣-cong (λ xx → b , fby , xx) (cancel⃖₂ x b gxb) ⟩
          (b , fby , gxb)
        ≣⟨⟩
          z
        ∎

rel-dagger : ∀ ℓ → Dagger (Relations ℓ)
rel-dagger ℓ = record
  { _† = flip
  ; identity = record
    { hither = λ _ _ → ≣-sym
    ; yon = λ _ _ → ≣-sym
    ; cancel⃗ = λ { x y ≣-refl → ≣-refl }
    ; cancel⃖ = λ { x y ≣-refl → ≣-refl }
    }
  ; homomorphism = λ {A} {B} {C} f g → record
    { hither = λ { c a (b , xx) → b , swap xx }
    ; yon = λ { c a (b , xx) → b , swap xx}
    ; cancel⃗ = {!!}
    ; cancel⃖ = {!!}
    }
  ; resp-≡ = λ x → record
    { hither = λ x₁ y → _≡ᴿ_.hither x y x₁
    ; yon = λ x₁ y → _≡ᴿ_.yon x y x₁
    ; cancel⃗ = λ x₁ y → _≡ᴿ_.cancel⃗ x y x₁
    ; cancel⃖ = λ x₁ y → _≡ᴿ_.cancel⃖ x y x₁
    }
  ; involutive = λ _ → ≡ᴿ-refl
  }
