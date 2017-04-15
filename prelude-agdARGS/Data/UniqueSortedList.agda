open import Prelude

open import prelude-agdARGS.Data.Infinities
open import prelude-agdARGS.Relation.Binary

module prelude-agdARGS.Data.UniqueSortedList
  {a e l : Level} (A : Set a) ⦃ STO : StrictTotalOrder {e = e} {l} A ⦄
  where

  infix 7 _■
  infixr 6 _,'_∷_
  data UniqueSortedList (lb ub : ∞[ A ]) : Set (a ⊔ l) where
    _■ : (lt : lb s< ub) → UniqueSortedList lb ub
    _,'_∷_ : ∀ hd (lt : lb s< (↑ hd)) (tl : UniqueSortedList (↑ hd) ub) → UniqueSortedList lb ub

  weaken : ∀ {a b c : ∞[ A ]} (pr : a s< b) → UniqueSortedList b c → UniqueSortedList a c
  weaken pr (lt ■)
    = <-trans {A = ∞[ A ]} pr lt ■
  weaken pr (hd ,' lt ∷ xs)
    = hd ,' <-trans {A = ∞[ A ]} pr lt ∷ xs
  
  insertUSL : ∀ a {lb ub} (lt₁ : lb s< (↑ a)) (lt₂ : (↑ a) s< ub)
              → UniqueSortedList lb ub → Maybe $ UniqueSortedList lb ub
  insertUSL a lt₁ lt₂ (lt ■)
    = just (a ,' lt₁ ∷ lt₂ ■)
  insertUSL a lt₁ lt₂ (hd ,' lt` ∷ xs)
    with stcompare {A = ∞[ A ]} (↑ a) (↑ hd)
  ... | less lt
    = just (a ,' lt₁ ∷ hd ,' lt ∷ xs)
  ... | equal eq
    = nothing
  ... | greater gt
    = fmap (hd ,' lt` ∷_) (insertUSL a gt lt₂ xs)
  
  insertUSL′ : ∀ a {lb ub} (lt₁ : lb s< (↑ a)) (lt₂ : (↑ a) s< ub)
            → UniqueSortedList lb ub → UniqueSortedList lb ub
  insertUSL′ a lt₁ lt₂ (_ ■)
    = a ,' lt₁ ∷ lt₂ ■
  insertUSL′ a lt₁ lt₂ xs'@(b ,' lt′ ∷ xs)
    with stcompare a b
  ... | less lt
    = a ,' lt₁ ∷ b ,' (↑ lt) ∷ xs
  ... | equal eq
    = xs'
  ... | greater gt
    = b ,' lt′ ∷ insertUSL′ a (↑ gt) lt₂ xs
  
  USLfromList : List A → Maybe $ UniqueSortedList -∞ +∞
  USLfromList = foldr (λ a mxs → mxs >>= insertUSL a (-∞<↑ a) (↑ a <+∞)) $ just (-∞<+∞ ■)
  
  module Membership where
    infix 5 _∈_
    data _∈_ (a : A) {lb ub : ∞[ A ]} : UniqueSortedList lb ub → Set (e ⊔ l) where
      zero : ∀ {xs} {lt} → a ∈ a ,' lt ∷ xs
      succ : ∀ {b xs} {lt} → a ∈ xs → a ∈ b ,' lt ∷ xs
  
    ∈∷-inj : ∀ {a hd} {lb : ∞[ A ]} {le : lb s< (↑ hd)} {ub} {xs : UniqueSortedList (↑ hd) ub}
             → a ∈ hd ,' le ∷ xs → Either (a ≡ hd) (a ∈ xs)
    ∈∷-inj zero = left refl
    ∈∷-inj (succ pr) = right pr
  
    -- would it have been simpler to use REL instead of Rel
    -- and remove f altogether?
    search : ∀ {ℓ} {B : Set ℓ} {R : Rel B ℓ} (d : Decidable R) (f : _ → B)
             → (a : B) {lb ub : _} (xs : UniqueSortedList lb ub)
             → Dec (Σ _ (λ el → el ∈ xs × R (f el) a))
    search d f a (lt ■) = no (λ { (_ , () , _)})
    search d f a (hd ,' lt ∷ xs) with d (f hd) a | search d f a xs
    ... | yes p | _
      = yes (hd , zero , p)
    ... | no x | (yes (el , el∈xs , p))
      = yes (el , succ el∈xs , p)
    ... | no ¬p | (no ¬q)
      = no (λ { (el , el∈hd∷xs , r)
                → either
                    (λ el≡hd → ¬p (transport _ el≡hd r))
                    (λ el∈xs → ¬q (el , el∈xs , r))
                    (∈∷-inj el∈hd∷xs)})
  
  module withEqDec ⦃ eqDec : Eq A ⦄ where
    open Membership
  
    _∈?_ : (a : _) {lb ub : ∞[ A ]} (xs : UniqueSortedList lb ub) → Dec (a ∈ xs)
    a ∈? xs with search _==_ id a xs
    ... | yes (.a , el∈xs , refl)
      = yes el∈xs
    ... | no ¬pr = no (λ a∈xs → ¬pr (_ , a∈xs , refl))
