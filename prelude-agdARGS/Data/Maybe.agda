module prelude-agdARGS.Data.Maybe where

open import Prelude

fromIsJust : ∀ {ℓ} {A : Set ℓ} (a : Maybe A) {pr : IsJust a} → A
fromIsJust (just x) = x
fromIsJust nothing {()}


