module prelude-agdARGS.Data.UniqueSortedList.Usual where

open import Prelude.String
open import prelude-agdARGS.Data.String

open import prelude-agdARGS.Data.UniqueSortedList _ ⦃ STO = StrictTotalOrderString ⦄ as USL public
open import prelude-agdARGS.Data.UniqueSortedList.SmartConstructors ⦃ STO = StrictTotalOrderString ⦄ public
open USL.withEqDec public
