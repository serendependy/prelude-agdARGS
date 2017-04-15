module prelude-agdARGS.Relation.Nullary where

open import Prelude

dec : ∀ {ℓ ℓ′} {A : Set ℓ} {P : Dec A → Set ℓ′} d
      → (∀ p → P (yes p)) → (∀ ¬p → P (no ¬p))
      → P d
dec (yes p) y n = y p
dec (no ¬p) y n = n ¬p

dec′ :  ∀ {ℓ ℓ′} {A : Set ℓ} {P : Set ℓ′} (d : Dec A)
        → (∀ p → P) → (∀ ¬p → P) → P
dec′ = dec

decToBool : ∀ {ℓ} {A : Set ℓ} → Dec A → Bool
decToBool d = dec d (const true) (const false)

IsYes : ∀ {ℓ} {A : Set ℓ} → Dec A → Set
IsYes = IsTrue ∘ decToBool

fromYes : ∀ {ℓ} {A : Set ℓ} (d : Dec A) {pr : IsYes d} → A
fromYes (yes p) = p
fromYes (no _) {()}
