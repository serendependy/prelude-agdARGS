module prelude-agdARGS.Algebra.Magma where

open import Prelude

record Magma {ℓ} (A : Set ℓ) : Set (lsuc ℓ) where
  field
    _∙_ : (x y : A) → A
open Magma ⦃ ... ⦄ public

fromMonoid : ∀ {ℓ} {A : Set ℓ} ⦃ _ : Monoid A ⦄ → Magma A
Magma._∙_ fromMonoid = _<>_

