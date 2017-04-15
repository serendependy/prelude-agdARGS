module prelude-agdARGS.System.Console.Options.Usual where

open import Prelude
  as Prelude hiding (Nat ; Int)

open import prelude-agdARGS.Level
open import prelude-agdARGS.Function
open import prelude-agdARGS.Data.Nat.Read
open import prelude-agdARGS.Data.Integer.Read
open import prelude-agdARGS.Data.List
open import prelude-agdARGS.Data.Error
open import prelude-agdARGS.Algebra.Magma
open import prelude-agdARGS.System.Console.Options.Domain public

Arguments : ∀ ℓ → Set (lsuc ℓ)
Arguments ℓ = Σ (Domain ℓ) (λ d → Parser d)

none : ∀ {ℓ} → Arguments ℓ
none = (Some (Lift ⊥)) , const (throw $ "Argument provided when none expected")

lotsOf : ∀ {ℓ} → Arguments ℓ → Arguments ℓ
lotsOf {ℓ} (d , p) = ALot (the (Magma (List _)) it) , ([_] <$>_) ∘ p

module Args where

  Regex = String
  regex : Arguments lzero
  regex = Some Regex , pure
  
  -- String
  string : Arguments lzero
  string = (Some String) , pure
  
  FilePath = String
  filePath : Arguments lzero
  filePath = Some FilePath , pure
  
  Regexp = String
  regexp : Arguments lzero
  regexp = Some Regexp , pure
  
  Url = String
  url : Arguments lzero
  url = Some Url , pure

  Nat : Arguments lzero
  Nat = Some Prelude.Nat , parseNatE

  Int : Arguments lzero
  Int = Some Prelude.Int , parseIntE
