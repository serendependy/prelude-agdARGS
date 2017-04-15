module prelude-agdARGS.Data.Char where

open import Prelude
open import Numeric.Nat.Properties
open import Agda.Builtin.Char

open import prelude-agdARGS.Relation.Binary
open import prelude-agdARGS.Data.Ord

instance
  StrictTotalOrderChar : StrictTotalOrder Char
  StrictTotalOrderChar = OrdToSTO _⟨<⟩_
