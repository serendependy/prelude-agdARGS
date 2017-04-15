module prelude-agdARGS.Data.List where

open import Prelude

open import prelude-agdARGS.Algebra.Magma

module _ {a : Level} {A : Set a} where

  init : List A → List A
  init xs = take (length xs - 1) xs
  
  breakAll : (p : A → Bool) (xs : List A) → List (List A)
  breakAll p xs =
    let (hd , tl) = foldr step ([] , []) xs
    in (if null hd then id else (hd ∷_)) tl
    where
      step : A → (List A × List (List A)) → (List A × List (List A))
      step a (xs , xss) = if p a then [] , xs ∷ xss else a ∷ xs , xss

instance
  MagmaList : ∀ {ℓ} {A : Set ℓ} → Magma (List A)
  MagmaList = record { _∙_ = _++_ }
