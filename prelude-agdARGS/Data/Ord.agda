module prelude-agdARGS.Data.Ord where

open import Prelude

open import prelude-agdARGS.Relation.Binary
open import prelude-agdARGS.Data.Equality

generalizeComparison : ∀ {a} {A : Set a} {x y} {_<_ : Rel A a}
                       → Comparison _<_ x y
                       → Comparison′ _≡_ _<_ x y
generalizeComparison (less lt)    = less lt
generalizeComparison (equal eq)   = equal eq
generalizeComparison (greater gt) = greater gt

OrdToSTO : ∀ {a} {A : Set a} ⦃ OrdA : Ord A ⦄
           → Transitive (Ord._<_ OrdA) → StrictTotalOrder A
StrictTotalOrder.super (OrdToSTO t)
  = defaultEquivalence
StrictTotalOrder._s<_ (OrdToSTO t)
  = Ord._<_ it
StrictTotalOrder.<-trans (OrdToSTO t)
  = t
StrictTotalOrder.stcompare (OrdToSTO t)
  = λ x y → generalizeComparison (compare x y)
