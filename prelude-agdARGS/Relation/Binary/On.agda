module prelude-agdARGS.Relation.Binary.On where

open import Prelude

open import prelude-agdARGS.Relation.Binary
--open import prelude-agdARGS.Function

module _ {a b e l : Level} {A : Set a} {B : Set b} (f : B → A) where

  reflexive : ∀ {ℓ} (~ : Rel A ℓ) → Reflexive ~ → Reflexive (~ on f)
  reflexive ~ ref = ref

  symmetric : ∀ {ℓ} (~ : Rel A ℓ) → Symmetric ~ → Symmetric (~ on f)
  symmetric ~ sym = sym

  transitive : ∀ {ℓ} (~ : Rel A ℓ) → Transitive ~ → Transitive (~ on f)
  transitive ~ trans = trans

  -- trichotomous : ∀ {e l} (≈ : Rel A e) (< : Rel A l)
  --                → (∀ x y → ((Comparison′ ≈) <) x y) → ∀ (x y : B) → (Comparison′ (≈ on f)) (< on f) x y
  -- trichotomous = {!!}

  trichotomous : ∀ {e l} (_≈_ : Rel A e) (_<_ : Rel A l)
                 → Trichotomous _≈_ _<_
                 → Trichotomous (_≈_ on f) (_<_ on f)
  trichotomous _≈_ _<_ compare x y
    with compare (f x) (f y)
  ... | less lt = less lt
  ... | equal eq = equal eq
  ... | greater gt = greater gt

  equivalence : Equivalence {r = e} A → Equivalence {r = e} B
  equivalence eq
    = record { _≈_ = _≈'_ on f
             ; ≈-refl  = reflexive _≈'_ (Equivalence.≈-refl eq)
             ; ≈-sym   = symmetric _≈'_ (Equivalence.≈-sym eq)
             ; ≈-trans = transitive _≈'_ (Equivalence.≈-trans eq) }
      where
      _≈'_ = Equivalence._≈_ eq

  strictTotalOrder : StrictTotalOrder {e = e} {l} A → StrictTotalOrder {e = e} {l} B
  strictTotalOrder sto =
    record { super = equivalence (StrictTotalOrder.super sto)
           ; _s<_  = _s<'_ on f
           ; <-trans = transitive _s<'_ (StrictTotalOrder.<-trans sto)
           ; stcompare = trichotomous _≈'_ _s<'_ (StrictTotalOrder.stcompare sto)
           }
    where
    _s<'_ = StrictTotalOrder._s<_ sto
    _≈'_  = Equivalence._≈_ ∘ StrictTotalOrder.super $ sto
