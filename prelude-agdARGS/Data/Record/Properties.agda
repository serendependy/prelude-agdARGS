open import Prelude

open import prelude-agdARGS.Relation.Binary

module prelude-agdARGS.Data.Record.Properties
  {a e l} {A : Set a} ⦃ STO : StrictTotalOrder {e = e} {l} A ⦄
  where

open import prelude-agdARGS.Data.Record
open import prelude-agdARGS.Data.UniqueSortedList A ⦃ STO = STO ⦄
open Membership

[lookupTabulate] : ∀ {ℓ} {lb ub} {args : UniqueSortedList lb ub}
                   → (p : ∀ {arg} → (pr : arg ∈ args) → Set ℓ)
                   → ∀ {arg} → (pr : arg ∈ args)
                   → [lookupR] pr ([tabulateR] args p) ≡ p pr
[lookupTabulate] p zero = refl
[lookupTabulate] p (succ pr) = [lookupTabulate] (p ∘ succ) pr

lookupTabulate : ∀ {ℓ} {lb ub} {args : UniqueSortedList lb ub}
                 → (p : ∀ {arg} → (pr : arg ∈ args) → Set ℓ)
                 → ∀ {arg} → (pr : arg ∈ args)
                 → lookupR pr (tabulateR p) ≡ p pr
lookupTabulate = [lookupTabulate]
