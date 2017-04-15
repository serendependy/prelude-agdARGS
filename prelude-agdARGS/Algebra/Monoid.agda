module prelude-agdARGS.Algebra.Monoid where

open import Prelude

open import prelude-agdARGS.Algebra.Magma

instance
  MonoidUnit : Monoid Unit
  mempty ⦃ MonoidUnit ⦄ = tt
  _<>_   ⦃ MonoidUnit ⦄ = const $ const tt

instance
  MonoidMaybeMagma : ∀ {ℓ} {A : Set ℓ} ⦃ _ : Magma A ⦄ → Monoid (Maybe A)
  mempty ⦃ MonoidMaybeMagma ⦄ = nothing
  _<>_   ⦃ MonoidMaybeMagma ⦄ = mproduct where
    mproduct : (x y : Maybe _) → Maybe _
    mproduct nothing nothing = nothing
    mproduct nothing (just y) = just y
    mproduct (just x) nothing = just x
    mproduct (just x) (just y) = just (x ∙ y)
