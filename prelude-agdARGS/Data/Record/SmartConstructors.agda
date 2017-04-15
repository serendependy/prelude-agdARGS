open import Prelude

open import prelude-agdARGS.Relation.Binary

module prelude-agdARGS.Data.Record.SmartConstructors
  {a e l : Level} {A : Set a} ⦃ STO : StrictTotalOrder {e = e} {l} A ⦄
  where

open import prelude-agdARGS.Relation.Nullary
open import prelude-agdARGS.Level
open import prelude-agdARGS.Data.Infinities
open import prelude-agdARGS.Data.UniqueSortedList A ⦃ STO ⦄ as USL
  hiding (module withEqDec)
open import prelude-agdARGS.Data.UniqueSortedList.SmartConstructors {A = A} ⦃ STO ⦄
open import prelude-agdARGS.Data.Record ⦃ STO ⦄ as Rec

⟨⟩ : ∀ {ℓ} → Record {ℓ} `[] _
⟨⟩ = _

infixr 5 _∷=_⟨_
_∷=_⟨_ : ∀ {ℓ} {args : USL} {f : Fields ℓ args} arg {S : Set ℓ}
         → S → Record args f
         → Record _ _
arg ∷= v ⟨ r = let open Rec.NeverFail in Rinsert arg (-∞<↑ arg) ↑ arg <+∞ v r

module withEqDec ⦃ eqDec : Eq A ⦄ where
  open USL.withEqDec ⦃ eqDec = eqDec ⦄

  `project : ∀ {ℓ lb ub} {args : UniqueSortedList lb ub} {f : Fields ℓ args} arg
             → Record args f → dec (arg ∈? args) (λ pr → lookupR pr f) (const $ Lift Unit)
  `project {args = args} arg r
    with arg ∈? args
  ... | yes pr = project pr r
  ... | no ¬pr = lift tt

  _‼_ : ∀ {ℓ} {lb ub} {args : UniqueSortedList lb ub} {f : Fields ℓ args}
        → Record args f → ∀ arg → {pr : IsYes (arg ∈? args)}
        → lookupR (fromYes (arg ∈? args) {pr}) f
  _‼_ {args = args} r arg {pr} with arg ∈? args
  ... | yes p = project p r
  _‼_ {_} {_} {_} {args} r arg {()} | no ¬p
