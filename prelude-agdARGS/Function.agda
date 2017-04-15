module prelude-agdARGS.Function where

open import Agda.Primitive

-- let's take a leaf from Idris's book
the : ∀ {ℓ} (A : Set ℓ) → A → A
the A a = a
