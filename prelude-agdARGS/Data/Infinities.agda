module prelude-agdARGS.Data.Infinities where

open import Prelude

open import prelude-agdARGS.Relation.Binary

infix 10 ↑_
data ∞[_] {ℓ} (A : Set ℓ) : Set ℓ where
  -∞ : ∞[ A ]
  ↑_ : A → ∞[ A ]
  +∞ : ∞[ A ]

infix 10 -∞≤_ _≤+∞
data [≤] {ℓᵃ ℓʳ} {A : Set ℓᵃ} (_≤_ : Rel A ℓʳ) :
     (a b : ∞[ A ]) → Set ℓʳ where
  -∞≤_ : (a : ∞[ A ])            → [≤] _≤_ -∞ a
  ↑_   : {a b : A} (le : a ≤ b)  → [≤] _≤_ (↑ a) (↑ b)
  _≤+∞ : (a : ∞[ A ])            → [≤] _≤_ a +∞

data [<] {ℓᵃ ℓʳ} {A : Set ℓᵃ} (_<_ : Rel A ℓʳ) :
     (a b : ∞[ A ]) → Set ℓʳ where
  -∞<↑_ : (a : A)                → [<] _<_ -∞ (↑ a)
  -∞<+∞ :                          [<] _<_ -∞ +∞
  ↑_<+∞ : (a : A)                → [<] _<_ (↑ a) +∞
  ↑_    : {a b : A} (lt : a < b) → [<] _<_ (↑ a) (↑ b)

data [≈] {ℓᵃ ℓᵉ} {A : Set ℓᵃ} (_≈_ : Rel A ℓᵉ) :
     (a b : ∞[ A ]) → Set ℓᵉ where
  -∞≈-∞ :                          [≈] _≈_ -∞ -∞
  ↑_    : {a b : A} (eq : a ≈ b) → [≈] _≈_ (↑ a) (↑ b)
  +∞≈+∞ :                          [≈] _≈_ +∞ +∞

_∞≈_ : ∀ {a r} {A : Set a} {_≈_ : Rel A r} {x y : A}
       → (a b : ∞[ A ])
       → Set r
_∞≈_ {_≈_ = _≈_} = [≈] _≈_

{-# DISPLAY [≈] _ a b = a ∞≈ b #-}

↑Comparison : ∀ {ℓ} {A : Set ℓ} {_<_ : Rel A ℓ} {x y : A}
              → Comparison _<_ x y
              → Comparison ([<] _<_) (↑ x) (↑ y)
↑Comparison (less lt) = less (↑ lt)
↑Comparison {x = x} (equal eq) = equal (transport (λ x' → ↑ x ≡ ↑ x') eq refl)
↑Comparison (greater gt) = greater (↑ gt)

↑LessEq : ∀ {ℓ} {A : Set ℓ} {_<_ : Rel A ℓ} {x y : A}
          → LessEq _<_ x y → LessEq ([<] _<_) (↑ x) (↑ y)
↑LessEq (less lt)    = less (↑ lt)
↑LessEq (equal refl) = equal refl

_∞<_ : ∀ {ℓᵃ ℓʳ} {A : Set ℓᵃ} {_<_ : Rel A ℓʳ}
       → (a b : ∞[ A ]) → Set ℓʳ
_∞<_ {_<_ = _<_} = [<] _<_

{-# DISPLAY [<] _ a b = a ∞< b #-}

instance
  Equivalence[≈] : ∀ {a e} {A : Set a} ⦃ _ : Equivalence {r = e} A ⦄ → Equivalence {r = e} (∞[ A ])
  Equivalence._≈_ Equivalence[≈]
    = [≈] _≈_

  Equivalence.≈-refl Equivalence[≈] { -∞}
    = -∞≈-∞
  Equivalence.≈-refl (Equivalence[≈] {A = A}) {↑ x₁}
    = ↑ ≈-refl {A = A}
  Equivalence.≈-refl Equivalence[≈] {+∞}
    = +∞≈+∞

  Equivalence.≈-sym Equivalence[≈] -∞≈-∞
    = -∞≈-∞
  Equivalence.≈-sym (Equivalence[≈] {A = A}) (↑ eq)
    = ↑ ≈-sym {A = A} eq
  Equivalence.≈-sym Equivalence[≈] +∞≈+∞
    = +∞≈+∞

  Equivalence.≈-trans Equivalence[≈] -∞≈-∞ y<z
    = y<z
  Equivalence.≈-trans (Equivalence[≈] {A = A}) (↑ x<y) (↑ y<z)
    = ↑ ≈-trans {A = A} x<y y<z
  Equivalence.≈-trans Equivalence[≈] +∞≈+∞ y<z = y<z

  StrictTotalOrderInf : ∀ {a e l} {A : Set a} ⦃ _ : StrictTotalOrder A ⦄
                        → StrictTotalOrder (∞[ A ])
  StrictTotalOrder.super (StrictTotalOrderInf {e = e})
    = Equivalence[≈] {e = e}
  StrictTotalOrder._s<_ (StrictTotalOrderInf {l = l})
    = [<] {ℓʳ = l} _s<_

  StrictTotalOrder.<-trans StrictTotalOrderInf (-∞<↑ a₁) ↑ .a₁ <+∞
    = -∞<+∞
  StrictTotalOrder.<-trans StrictTotalOrderInf (-∞<↑ a₁) (↑ x<y)
    = -∞<↑ _
  StrictTotalOrder.<-trans StrictTotalOrderInf -∞<+∞ ()
  StrictTotalOrder.<-trans StrictTotalOrderInf ↑ a₁ <+∞ ()
  StrictTotalOrder.<-trans StrictTotalOrderInf (↑ x<y) ↑ a₁ <+∞
    = ↑ _ <+∞
  StrictTotalOrder.<-trans (StrictTotalOrderInf {A = A}) (↑ x<y) (↑ y<z)
    = ↑ <-trans {A = A} x<y y<z

  StrictTotalOrder.stcompare StrictTotalOrderInf -∞ -∞
    = equal -∞≈-∞
  StrictTotalOrder.stcompare StrictTotalOrderInf -∞ (↑ y)
    = less (-∞<↑ y)
  StrictTotalOrder.stcompare StrictTotalOrderInf -∞ +∞
    = less -∞<+∞
  StrictTotalOrder.stcompare StrictTotalOrderInf (↑ x) -∞
    = greater (-∞<↑ x)
  StrictTotalOrder.stcompare StrictTotalOrderInf (↑ x) (↑ y)
    with stcompare x y
  ... | less lt
    = less (↑ lt)
  ... | equal eq
    = equal (↑ eq)
  ... | greater gt
    = greater (↑ gt)
  StrictTotalOrder.stcompare StrictTotalOrderInf (↑ x) +∞
    = less ↑ x <+∞
  StrictTotalOrder.stcompare StrictTotalOrderInf +∞ -∞
    = greater -∞<+∞
  StrictTotalOrder.stcompare StrictTotalOrderInf +∞ (↑ x)
    = greater ↑ x <+∞
  StrictTotalOrder.stcompare StrictTotalOrderInf +∞ +∞
    = equal +∞≈+∞
