module prelude-agdARGS.Data.Record.Usual where

open import Prelude.String
open import prelude-agdARGS.Data.String

open import prelude-agdARGS.Data.UniqueSortedList.Usual public
  hiding (module NeverFail)
open import prelude-agdARGS.Data.Record ⦃ STO = StrictTotalOrderString ⦄
  as Rec public
open import prelude-agdARGS.Data.Record.SmartConstructors ⦃ STO = StrictTotalOrderString ⦄
  as SC public hiding (module withEqDec)
open SC.withEqDec public

open Membership public
