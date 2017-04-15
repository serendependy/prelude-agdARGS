module prelude-agdARGS.Data.Equality where

open import Prelude

open import prelude-agdARGS.Relation.Binary

defaultEquivalence : ∀ {a} {A : Set a} → Equivalence A
Equivalence._≈_ defaultEquivalence
  = _≡_
Equivalence.≈-refl defaultEquivalence
  = refl
Equivalence.≈-sym defaultEquivalence
  = sym
Equivalence.≈-trans defaultEquivalence
  = trans
