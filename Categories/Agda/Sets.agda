module Categories.Agda.Sets where

open import Level
open import Categories.Category
open import Categories.Agda using (Sets)

C : Category _ _ _
C = Sets zero

open import Categories.Morphisms C
open import Categories.Equalizer C

open import Data.Bool

open Category C

sets-mono-equalizer : ∀ {A B E : Obj} {i : E ⇒ A} → Mono i → ∃[ (f , g) ∈ (A ⇒ B, A ⇒ B) ] {!Equalizer E f g!}
sets-mono-equalizer = {!!}
