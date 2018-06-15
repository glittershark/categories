module Categories.Agda.Functors where

open import Categories.Agda
open import Categories.Category
open import Categories.Functor

r→-functor : ∀ ℓ → Set ℓ →  Endofunctor (Sets ℓ)
r→-functor ℓ r = record
  { F₀ = λ x → {!r → x!}
  }
