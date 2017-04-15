module prelude-agdARGS.Relation.Binary where

open import Prelude

------------------------------------------------------------------------
-- Binary relations

-- Homogeneous binary relations

REL : ∀ {a b} → Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ lsuc ℓ)
REL A B ℓ = A → B → Set ℓ

Rel : ∀ {a} → Set a → (ℓ : Level) → Set (a ⊔ lsuc ℓ)
Rel A ℓ = REL A A ℓ

-- Reflexivity
Reflexive : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
Reflexive _~_ = ∀ {x} → x ~ x

Symmetric : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
Symmetric _~_ = ∀ {x y} → x ~ y → y ~ x

-- Transitivity

Transitive : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
Transitive _~_ = ∀ {x y z} → x ~ y → y ~ z → x ~ z

-- Decidable

Decidable : ∀ {a b ℓ} {A : Set a} {B : Set b} → REL A B ℓ → Set _
Decidable _~_ = ∀ x y → Dec (x ~ y)

-- Generalized comparison
data Comparison′ {a e r} {A : Set a}
                 (_≈_ : Rel A e) (_<_ : Rel A r) (x y : A)
                 : Set (a ⊔ e ⊔ r)
     where
  less    : (lt : x < y) → Comparison′ _≈_ _<_ x y
  equal   : (eq : x ≈ y) → Comparison′ _≈_ _<_ x y
  greater : (gt : y < x) → Comparison′ _≈_ _<_ x y

Trichotomous : ∀ {a e l} {A : Set a} → Rel A e → Rel A l → Set _
Trichotomous _≈_ _<_ = ∀ x y → Comparison′ _≈_ _<_ x y

--------------------------------------------------------------------------------
-- Equivalence Relations

record Equivalence {a r} (A : Set a) : Set (a ⊔ lsuc r) where
  field
    _≈_ : Rel A r
    ≈-refl  : Reflexive  _≈_
    ≈-sym   : Symmetric  _≈_
    ≈-trans : Transitive _≈_

open Equivalence ⦃ ... ⦄ public
{-# DISPLAY Equivalence._≈_ a b = a ≈ b #-}

record StrictTotalOrder {a e l} (A : Set a) : Set (a ⊔ lsuc e ⊔ lsuc l) where
  field
    overlap ⦃ super ⦄ : Equivalence {r = e } A
    _s<_ : Rel A l
    <-trans : Transitive _s<_
    stcompare : ∀ (x y : A) → Comparison′ _≈_ _s<_ x y

open StrictTotalOrder ⦃ ... ⦄ public
{-# DISPLAY StrictTotalOrder._s<_ a b = a s< b #-}
