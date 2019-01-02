module Categories.Agda.Sets.Functors {ℓ} where

open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.List using (List)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
import Data.List as L
open import Categories.Category
open import Categories.Agda
open import Categories.Functor hiding (_≡_) renaming (_∘_ to _∘ᶠ_; id to idᶠ)
open import Categories.Monad
open import Categories.Support.PropositionalEquality
open import Function using (const; _$_)
open import Categories.NaturalTransformation using (NaturalTransformation; _∘₁_; _∘ˡ_) renaming (_≡_ to _≡ₙₜ_)

open Category (Sets ℓ)

module MaybeFunctor where
  maybe-functor : Endofunctor (Sets ℓ)
  maybe-functor = record
    { F₀ = Maybe
    ; F₁ = Maybe.map
    ; identity = identity
    ; homomorphism = λ { {x = x} → homomorphism {x = x} }
    ; F-resp-≡ = F-resp-≡
    }
   where
    .identity : ∀ {A} → Maybe.map (id {A}) ≡ id
    identity {x = just _}  = ≣-refl
    identity {x = nothing} = ≣-refl

    homomorphism
      : {X Y Z : Obj} {f : X ⇒ Y} {g : Y ⇒ Z}
      → Maybe.map (g ∘ f) ≡ (Maybe.map g ∘ Maybe.map f)
    homomorphism {x = just _}  = ≣-refl
    homomorphism {x = nothing} = ≣-refl

    F-resp-≡ : {A B : Obj} {F G : A ⇒ B}
            → F ≡ G → Maybe.map F ≡ Maybe.map G
    F-resp-≡ eq {just _} = ≣-cong just eq
    F-resp-≡ _ {nothing} = ≣-refl

  maybe-monad : Monad (Sets ℓ)
  maybe-monad = record
    { F = maybe-functor
    ; η = η
    ; μ = μ
    ; assoc = λ { {_} {just _} → ≣-refl ; {_} {nothing} → ≣-refl }
    ; identityʳ = ≣-refl
    ; identityˡ = λ { {_} {just _} → ≣-refl ; {_} {nothing} → ≣-refl }
    }
   where
    join′ : ∀ {X} → Maybe (Maybe X) → Maybe X
    join′ (just x) = x
    join′ nothing = nothing

    maybe² : Endofunctor (Sets ℓ)
    maybe² = maybe-functor ∘ᶠ maybe-functor

    μ-commute : ∀ {X Y} → (f : X ⇒ Y) →
      CommutativeSquare (Functor.F₁ maybe² f) join′ join′ (Maybe.map f)
    μ-commute _ {just x} = ≣-refl
    μ-commute _ {nothing} = ≣-refl

    η : NaturalTransformation idᶠ maybe-functor
    η = record { η = λ _ → just ; commute = λ _ → ≣-refl }
    μ : NaturalTransformation maybe² maybe-functor
    μ = record { η = λ _ → join′ ; commute = μ-commute }

  MaybeT : Monad (Sets ℓ) → Monad (Sets ℓ)
  MaybeT m =
    record
      { F = Monad.F m ∘ᶠ maybe-functor
      ; η = record { η = λ _ →  return[ m ] ∘ just
                    ; commute = λ f → commute (η m) $ fmap[ maybe-functor ] f
                    }
      ; μ = record { η = λ _ → join-maybet m
                    ; commute = μ-commute m
                    }
      ; assoc = {!!}
      ; identityˡ = {!!}
      ; identityʳ = {!!}
      }
   where
    open Monad
    open NaturalTransformation using (commute) renaming (η to ηⁿ)

    join-maybet
      : ∀ (m : Monad (Sets ℓ)) {A : Set ℓ}
      → let open Monad m renaming (F to M) in
        M ⟨ Maybe (M ⟨ Maybe A ⟩₀) ⟩₀
      → M ⟨ Maybe A ⟩₀
    join-maybet m = join[ m ] ∘ fmap[ F m ] λ
      { (just x) → x
      ; nothing  → return[ m ] nothing
      }

    .μ-commute
      : ∀ (m : Monad (Sets ℓ)) {X Y : Set ℓ} (f : X → Y)
          {x : (F m) ⟨ Maybe ( (F m) ⟨ Maybe X ⟩₀ ) ⟩₀}
      → (join-maybet m ∘ fmap[ F m ∘ᶠ maybe-functor ∘ᶠ F m ∘ᶠ maybe-functor ] f $ x)
      ≣ (fmap[ F m ∘ᶠ maybe-functor ] f ∘ join-maybet m $ x)
    μ-commute m f {x} = let open ≣-reasoning in
      begin
        (join-maybet m ∘ fmap[ F m ∘ᶠ maybe-functor ∘ᶠ F m ∘ᶠ maybe-functor ] f $ x)
      ≣⟨ {!!} ⟩
        (fmap[ F m ∘ᶠ maybe-functor ] f ∘ join-maybet m $ x)
      ∎

  open Monad
  open NaturalTransformation using (commute) renaming (η to ηⁿ)

  hoist-maybet
    : ∀ {A B : Monad (Sets ℓ)}
    → NaturalTransformation (F A) (F B)
    → NaturalTransformation (F A ∘ᶠ maybe-functor) (F B ∘ᶠ maybe-functor)
  hoist-maybet {A} {B} m-morph = record
    { η = λ X → ηⁿ m-morph (Maybe X)
    ; commute = commute m-morph ∘ fmap[ maybe-functor ]
    }

  maybeT-mmonad : Monad (Monads (Sets ℓ))
  maybeT-mmonad = record
    { F = functor
    ; η = {!!}
    ; μ = {!!}
    ; assoc = {!!}
    ; identityˡ = {!!}
    ; identityʳ = {!!}
    }
   where
    open Monad
    open NaturalTransformation using (commute) renaming (η to ηⁿ)
    functor : Endofunctor (Monads (Sets ℓ))
    functor = record
      { F₀ = MaybeT
      ; F₁ = hoist-maybet
      ; identity = {!!}
      ; homomorphism = {!!}
      ; F-resp-≡ = {!!}
      }


open MaybeFunctor public

module ListFunctor where

  list-functor : Endofunctor (Sets ℓ)
  list-functor = record
    { F₀ = List
    ; F₁ = L.map
    ; identity = identity
    ; homomorphism = homomorphism
    ; F-resp-≡ = F-resp-≡
    }
   where
    open L.List

    .identity : ∀ {A} → L.map (id {A}) ≡ id
    identity {x = []} = ≣-refl
    identity {x = x ∷ x₁} = ≣-cong (_∷_ x) identity

    homomorphism
      : {X Y Z : Obj} {f : X ⇒ Y} {g : Y ⇒ Z}
      → L.map (g ∘ f) ≡ (L.map g ∘ L.map f)
    homomorphism {x = []} = ≣-refl
    homomorphism {f = f} {g = g} {x = x ∷ x₁} =
      ≣-cong (_∷_ ∘ g ∘ f $ x) homomorphism

    .F-resp-≡ : {A B : Obj} {F G : A ⇒ B}
            → F ≡ G → L.map F ≡ L.map G
    F-resp-≡ eq {[]} = ≣-refl
    F-resp-≡ {F = F} {G = G} eq {l@(x ∷ xs)} = let open ≣-reasoning in
      begin
        L.map F l
      ≣⟨ ≣-cong (λ x′ → x′ ∷ L.map F xs) eq ⟩
        G x ∷ L.map F xs -- the head is the same
      ≣⟨ ≣-cong (λ xs′ → G x ∷ xs′) (F-resp-≡ eq) ⟩
        G x ∷ L.map G xs -- recurse to make the rest the same
      ≣⟨⟩
        L.map G l -- by definition of map
      ∎

  list-monad : Monad (Sets ℓ)
  list-monad = record
    { F = list-functor
    ; η = record { η = λ _ x → x ∷ [] ; commute = λ _ → ≣-refl }
    ; μ = record { η = λ _ → L.concat ; commute = μ-commute }
    ; assoc = λ {_} {x} → assoc′ x
    ; identityˡ = λ {_} {xs} → identityˡ′ xs
    ; identityʳ =  λ {_} {xs} → ++-identityʳ xs
    }
   where
    open L.List
    open Data.List using (_++_)

    .μ-commute
      : ∀ {X Y} → (f : X → Y)
      → CommutativeSquare
        (Functor.F₁ (list-functor ∘ᶠ list-functor) f)
        L.concat
        L.concat
        (L.map f)
    μ-commute f {[]} = ≣-refl
    μ-commute f {[] ∷ xs} = μ-commute f {xs}
    μ-commute {X} {Y} f {l₁@(l₂@(x ∷ xs₁) ∷ xs₂)} = let open ≣-reasoning in begin
        (L.concat ∘ Functor.F₁ (list-functor ∘ᶠ list-functor) f $ l₁)
      ≣⟨⟩
        (L.concat ∘ L.map (L.map f) $ l₁)
      ≣⟨⟩
        (L.map f l₂ ++ L.concat (L.map (L.map f) xs₂))
      ≣⟨ ≣-cong (λ xs → L.map f l₂ ++ xs) $ μ-commute f {xs₂} ⟩
        (L.map f l₂ ++ L.map f (L.concat xs₂))
      ≣⟨ ≣-cong (λ xs → f x ∷ xs) $ lem₁ (xs₁) (xs₂) ⟩
        (L.map f ∘ L.concat $ l₁)
      ∎
     where
      lem₁ : (xs₁ : List X)
            (xs₂ : List (List X))
          → L.map f xs₁ ++ L.map f (L.concat xs₂)
          ≣ L.map f (xs₁ ++ L.concat xs₂)
      lem₁ [] _ = ≣-refl
      lem₁ (x ∷ xs₁) xs₂  = ≣-cong (λ xs → f x ∷ xs) $ lem₁ xs₁ xs₂

    assoc′
      : ∀ {A : Set ℓ}
          (x : List (List (List A)))
      → L.concat (L.map L.concat x) ≣ L.concat (L.concat x)
    assoc′ [] = ≣-refl
    assoc′ ([] ∷ xs) = assoc′ xs
    assoc′ (([] ∷ x₂) ∷ xs) = assoc′ (x₂ ∷ xs)
    assoc′ (((x ∷ x₁) ∷ x₂) ∷ xs) = ≣-cong (x ∷_) (assoc′ ((x₁ ∷ x₂) ∷ xs))

    identityˡ′
      : ∀ {A : Set ℓ}
          (xs : List A)
      → L.concat (L.map (_∷ []) xs) ≣ xs
    identityˡ′ [] = ≣-refl
    identityˡ′ (x ∷ xs) = ≣-cong (x ∷_) $ identityˡ′ xs

open ListFunctor public
