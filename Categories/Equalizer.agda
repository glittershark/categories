{-# OPTIONS --allow-unsolved-metas #-}
open import Categories.Category

module Categories.Equalizer {o} {ℓ} {e} (C : Category o ℓ e) where

open Category C
open Equiv
open import Data.Fin
open import Function using (_∋_; _$_)
open import Level using (_⊔_)
open import Data.Product
open import Categories.Morphisms C
open import Categories.Support.PropositionalEquality
open import Categories.Functor using (Functor; _⟨_⟩₀; _⟨_⟩₁)
open import Categories.Limit
open import Categories.Cone
open LimitsOf

record Equalizer {A B : Obj} (E : Obj) (f g : A ⇒ B) : Set (o ⊔ ℓ ⊔ e) where
  field
    i : E ⇒ A
    .eq : f ∘ i ≡ g ∘ i
    .univ
      : {C : Obj} (h : C ⇒ A)
      → (f ∘ h ≡ g ∘ h)
      → Σ[ k ∈ C ⇒ E ]
        i ∘ k ≡ h
      × (∀ j → (i ∘ j ≡ h) → j ≡ k)

  .mono : Mono i
  mono j l i∘j≡i∘l =
    let open HomReasoning
        h = i ∘ j
        k , i∘k≡h , k-univ = univ h $
          begin
            f ∘ i ∘ j
          ↑⟨ assoc ⟩
            (f ∘ i) ∘ j
          ↓⟨ eq ⟩∘⟨ refl ⟩
            (g ∘ i) ∘ j
          ↓⟨ assoc ⟩
            g ∘ i ∘ j
          ∎
        j≡k : j ≡ k
        j≡k = k-univ j refl

        l≡k : l ≡ k
        l≡k = k-univ l (sym i∘j≡i∘l)

    in trans j≡k $ sym l≡k

  .epi-iso : Epi i → Σ[ k ∈ A ⇒ E ] (Iso i k)
  epi-iso epi =
    let open HomReasoning
        f≡g : f ≡ g
        f≡g = epi f g eq

        k , i∘k≡id , k-univ = univ id $
          begin
            f ∘ id
          ↓⟨ identityʳ ⟩
            f
          ↓⟨ f≡g ⟩
            g
          ↑⟨ identityʳ ⟩
            g ∘ id
          ∎

        k∘i≡id : k ∘ i ≡ id
        k∘i≡id = mono (k ∘ i) id $
          begin
            i ∘ (k ∘ i)
          ↑⟨ assoc ⟩
            (i ∘ k) ∘ i
          ↓⟨ i∘k≡id ⟩∘⟨ refl ⟩
            id ∘ i
          ↓⟨ identityˡ ⟩
            i
          ↑⟨ identityʳ ⟩
            i ∘ id
          ∎

    in k , (record { isoˡ = k∘i≡id ; isoʳ = i∘k≡id })

-- ⊑
-- ⊑

id-eq : ∀ {A B : Obj} (f : A ⇒ B) → Equalizer A f f
id-eq f = record
  { i = id
  ; eq = refl
  ; univ = λ h _ → h , identityˡ , λ _ → trans $ sym identityˡ
  }

-- the domain of the diagram that describes an equalizer
data eq-diag-⇒ : Fin 2 → Fin 2 → Set where
  f   : eq-diag-⇒ (# 0) (# 1)
  g   : eq-diag-⇒ (# 0) (# 1)
  id′ : ∀ {n : Fin 2} → eq-diag-⇒ n n

eq-diag : Category _ _ _
eq-diag = record
  { Obj = Fin 2
  ; _⇒_ = eq-diag-⇒
  ; _≡_ = _≣_
  ; _∘_ = _∘′_
  ; id  = id′
  ; assoc = assoc′
  ; identityˡ = λ { {f = f} → ≣-refl ; {f = g} → ≣-refl ; {f = id′} → ≣-refl }
  ; identityʳ = λ { {f = f} → ≣-refl ; {f = g} → ≣-refl ; {f = id′} → ≣-refl }
  ; ∘-resp-≡ = {!!}
  ; equiv = ≣-isEquivalence
  }
  where
    _∘′_ : ∀ {A B C} → eq-diag-⇒ B C → eq-diag-⇒ A B → eq-diag-⇒ A C
    f ∘′ id′   = f
    g ∘′ id′   = g
    id′ ∘′ f   = f
    id′ ∘′ g   = g
    id′ ∘′ id′ = id′

    assoc′ : ∀ {A B C D}
               {f′ : eq-diag-⇒ A B}
               {g′ : eq-diag-⇒ B C}
               {h′ : eq-diag-⇒ C D}
           → ((h′ ∘′ g′) ∘′ f′) ≣ (h′ ∘′ (g′ ∘′ f′))
    assoc′ {f′ = f} {id′} {id′}   = ≣-refl
    assoc′ {f′ = g} {id′} {id′}   = ≣-refl
    assoc′ {f′ = id′} {f} {id′}   = ≣-refl
    assoc′ {f′ = id′} {g} {id′}   = ≣-refl
    assoc′ {f′ = id′} {id′} {f}   = ≣-refl
    assoc′ {f′ = id′} {id′} {g}   = ≣-refl
    assoc′ {f′ = id′} {id′} {id′} = ≣-refl

limit→eq : (J : Functor eq-diag C) → (lim : Limit J) → Equalizer (Limit.vertex lim) (J ⟨ f ⟩₁) (J ⟨ g ⟩₁)
limit→eq J lim = record
  { i = proj (# 0)
  ; eq = eq
  ; univ =  λ {A} → univ A
  }
  where
    open Limit lim
    open HomReasoning
    .eq : (J ⟨ f ⟩₁) ∘ proj (# 0) ≡ (J ⟨ g ⟩₁) ∘ proj (# 0)
    eq =
      begin
        J ⟨ f ⟩₁ ∘ proj (# 0)
      ↓⟨ Cone.commute proj-cone f ⟩
        proj (# 1)
      ↑⟨ Cone.commute proj-cone g ⟩
        J ⟨ g ⟩₁ ∘ proj (# 0)
      ∎
    .univ
      : ∀ (A : Obj)
          (h : A ⇒ (J ⟨ # 0 ⟩₀))
      → (J ⟨ f ⟩₁) ∘ h ≡ (J ⟨ g ⟩₁) ∘ h
      → Σ[ k ∈ (A ⇒ vertex) ]
        proj (# 0) ∘ k ≡ h
      × ((j : A ⇒ vertex) → proj (# 0) ∘ j ≡ h → j ≡ k)
    univ A h J⟨f⟩∘h≡J⟨g⟩h
      = k
      , k-eq
      , {!!}
      where
        .k-cone : ConeOver.Cone J
        k-cone = record
          { N = A
          ; ψ =  λ
            { zero → h
            ; (suc zero) → J ⟨ f ⟩₁ ∘ h
            ; (suc (suc ()))
            }
          ; commute = λ
            { f → {!!}
            ; g → {!!}
            ; id′ → {!!}
            }
          }
        .k : A ⇒ vertex
        k = rep {!k-cone!} -- rep k-cone

        .k-eq : proj (# 0) ∘ k ≡ h
        k-eq =
         begin
           proj (# 0) ∘ k
         ↓⟨ {!commute _ (# 0)!} ⟩
           {!!}
         ↓⟨ {!!} ⟩
           h
         ∎
