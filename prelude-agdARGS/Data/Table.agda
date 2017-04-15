module prelude-agdARGS.Data.Table where

open import Prelude

open import prelude-agdARGS.Data.String as String
open import prelude-agdARGS.Data.Vec

Table : ∀ {ℓ} → (m n : Nat) (A : Set ℓ) → Set ℓ
Table m n A = Vec (Vec A n) m

infixr 3 _∥_
_∥_ : ∀ {ℓ} {A : Set ℓ} {m n p} → Table m n A → Table m p A → Table m (n + p) A
xs ∥ ys = vzipWith _v++_ xs ys

private
  pureTab : ∀ {a} {m n} {A : Set a}
            → A → Table m n A
  pureTab = pure {F = flip Vec _} ∘ pure

  infixl 3 _⊛_
  _⊛_ : ∀ {a b} {A : Set a} {B : Set b} {m n : Nat}
        → (fs : Table m n (A → B)) (as : Table m n A)
        → Table m n B
  fs ⊛ as = _<*>′_ <$>′ fs <*>′ as

instance
  FunctorTable : ∀ {a} {m n} → Functor {a} (Table m n)
  Functor.fmap FunctorTable = fmap {F = flip Vec _} ∘ fmap

  FunctorTable′ : ∀ {a b} {m n} → Functor′ {a} {b} (Table m n)
  Functor′.fmap′ FunctorTable′ = fmap′ {F = flip Vec _} ∘ fmap′

  ApplicativeTable : ∀ {a} {m n} → Applicative {a} (Table m n)
  Applicative.pure ApplicativeTable = pureTab
  Applicative._<*>_ ApplicativeTable = _⊛_

  ApplicativeTable′ : ∀ {a b} {m n} → Applicative′ {a} {b} (Table m n)
  Applicative′._<*>′_ ApplicativeTable′ = _⊛_

module _ {a b c : Level} {A : Set a} {B : Set b} {C : Set c} where

  tzipWith : ∀ {m n} (f : A → B → C) → Table m n A → Table m n B
             → Table m n C
  tzipWith f ta tb = (pure {F = Table _ _} f) <*>′ ta <*>′ tb


private
  showTable : ∀ {a} {m n} {A : Set a} ⦃ _ : Show A ⦄
              → Table m n A → String
  showTable {n = n} ta = unlines $ uncurry (flip _$_) res where
    P : Set
    P = Vec Nat n × (Vec Nat n → List String)

    showCell : String → Nat → String
    showCell str n = str & (fromVec {n = 2 + n - stringLength str} $ pure ' ')

    cons : Vec String n → P → P
    cons row (ms , str) =
      let strs-lengths = fmap stringLength row
          ns           = vzipWith max ms strs-lengths
      in ns , λ ls → (concatVec $ vzipWith showCell row ls) ∷ str ls

    res : P
    res = vfoldr (λ xs p → cons xs p) (pure 0 , const []) (fmap′ {F = Table _ _} ((_& "\n") ∘ show) ta)

instance
  ShowTable : ∀ {a} {m n} {A : Set a} ⦃ _ : Show A ⦄
              → Show (Table m n A)
  ShowTable = simpleShowInstance showTable
