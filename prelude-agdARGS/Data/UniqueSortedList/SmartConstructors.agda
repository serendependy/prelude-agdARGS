open import Agda.Primitive
open import prelude-agdARGS.Relation.Binary
open import prelude-agdARGS.Data.Maybe
open import prelude-agdARGS.Data.Infinities

module prelude-agdARGS.Data.UniqueSortedList.SmartConstructors
  {a e l : Level} {A : Set a} ⦃ STO : StrictTotalOrder {e = e} {l} A ⦄ where

open import prelude-agdARGS.Data.UniqueSortedList A ⦃ STO = STO ⦄

USL : Set (l ⊔ a)
USL = UniqueSortedList -∞ +∞

`[] : USL
`[] = -∞<+∞ ■

module MayFail where
  infixr 5 _`∷_
  _`∷_ : ∀ x (xs : USL) {pr : _} → USL
  (x `∷ xs) {pr} = fromIsJust (insertUSL x (-∞<↑ x) ↑ x <+∞ xs) {pr}

module NeverFail where
  infixr 5 _`∷_
  _`∷_ : ∀ x (xs : USL)  → USL
  (x `∷ xs) = insertUSL′ x (-∞<↑ x) ↑ x <+∞ xs

infix 6 `[_]
`[_] : ∀ x → USL
`[ x ] = fromIsJust (insertUSL x (-∞<↑ x) ↑ x <+∞ `[])
