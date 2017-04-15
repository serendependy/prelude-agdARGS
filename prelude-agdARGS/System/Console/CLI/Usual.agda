module prelude-agdARGS.System.Console.CLI.Usual where

open import Prelude

open import prelude-agdARGS.System.Console.CLI
open import prelude-agdARGS.System.Console.CLI.Parser

err : String → IO _
err = putStrLn ∘ ("*** Error: " <>_)

withCLI : ∀ {ℓ} (c : CLI ℓ) (k : ParsedCommand (exec c) → IO Unit) → _
withCLI c k = getArgs >>= λ args → either err k (parseInterface c args)
