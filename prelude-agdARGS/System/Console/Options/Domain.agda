module prelude-agdARGS.System.Console.Options.Domain where

open import Prelude

open import prelude-agdARGS.Algebra.Magma
open import prelude-agdARGS.Data.Error

data Domain (ℓ : Level) : Set (lsuc ℓ) where
  Some : (S : Set ℓ) → Domain ℓ
  ALot : {S : Set ℓ} → (M : Magma S) → Domain ℓ

elimDomain : ∀ {d p} {P :  Domain d → Set p}
             → (dSome : ∀ S → P (Some S))
             → (dALot : ∀ {S} M → P (ALot {S = S} M))
             → (d : Domain d)
             → P d
elimDomain dSome dALot (Some S) = dSome S
elimDomain dSome dALot (ALot M) = dALot M

Carrier : ∀ {ℓ} → Domain ℓ → Set ℓ
Carrier = elimDomain id (λ {S} _ → S)

Parser : ∀ {ℓ} → Domain ℓ → Set ℓ
Parser d = String → Error (Carrier d)
