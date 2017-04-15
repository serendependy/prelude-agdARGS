module prelude-agdARGS.Data.Nat.Read where

open import Prelude
open import prelude-agdARGS.Data.Error


parseHexDigit : Char → Maybe Nat
parseHexDigit c
  with isDigit c
... | true
  = just (charToNat c - charToNat '0')
... | false
  with elem c (unpackString "ABCDEF")
... | true
  = just (10 + charToNat c - charToNat 'A')
... | false
  = nothing

parseBase : (base : Nat) ⦃ base≥2 : IsTrue (2 ≤? base) ⦄ ⦃ base≤16 : IsTrue (base ≤? 16) ⦄
            → Char → Maybe Nat
parseBase base c =
  parseHexDigit c >>= λ d →
  if (suc d ≤? base) then just d else nothing

parseNatE : String → Error Nat
parseNatE str
  = maybe (throw $ "Invalid natural number " & str)
          pure
          (goBase ∘ unpackString $ str)
  where
  go : (base : Nat) ⦃ base≥2 : IsTrue (base ≥? 2) ⦄ ⦃ base≤16 : IsTrue (base ≤? 16) ⦄
       → List Char → Maybe Nat
  go base = foldl step (just 0) where
    step : Maybe Nat → Char → Maybe Nat
    step acc c =
      acc >>= λ acc' →
      parseBase base c >>= λ d →
      pure $ acc' * base + d

  goBase : List Char → Maybe Nat
  goBase ('0' ∷ 'x' ∷ xs) = go 16 xs
  goBase ('0' ∷ 'b' ∷ xs) = go 2 xs
  goBase xs               = go 10 xs

private
  test : _
  test = parseNatE "0xFF1"
