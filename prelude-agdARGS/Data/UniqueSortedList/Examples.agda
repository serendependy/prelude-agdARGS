module prelude-agdARGS.Data.UniqueSortedList.Examples where

open import Prelude.String
open import prelude-agdARGS.Data.UniqueSortedList
open import prelude-agdARGS.Data.UniqueSortedList.SmartConstructors {A = String}
open import prelude-agdARGS.Data.String

Characteristics : USL
Characteristics = let open MayFail in "name" `∷ "age" `∷ "idcard" `∷ `[]

Characteristics′ : USL
Characteristics′ = let open NeverFail in "name" `∷ "age" `∷ "idcard" `∷ `[]
