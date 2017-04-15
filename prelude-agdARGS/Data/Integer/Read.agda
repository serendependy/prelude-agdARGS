module prelude-agdARGS.Data.Integer.Read where

open import Prelude
open import prelude-agdARGS.Data.Error
open import prelude-agdARGS.Data.Nat.Read

parseIntE : String → Error Int
parseIntE str
  = either (throw ∘ ("Invalid integer: " &_))
           pure
           (go ∘ unpackString $ str)
  where
  go : List Char → Error Int
  go ('-' ∷ n) = mapEither id neg (parseNatE ∘ packString $ n)
  go n         = mapEither id pos (parseNatE ∘ packString $ n)
