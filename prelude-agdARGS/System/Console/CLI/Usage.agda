module prelude-agdARGS.System.Console.CLI.Usage where

open import Prelude

open import prelude-agdARGS.Level
open import prelude-agdARGS.Data.String hiding (unlines)
open import prelude-agdARGS.Data.Record.Usual as RU
open import prelude-agdARGS.System.Console.CLI

Printer : Set
Printer = Nat → List String -- indentation level

indent : Nat → String → String
indent i str = packString (replicate i ' ') <> str

open import prelude-agdARGS.System.Console.Modifiers

namedString : (name str : String) → String
namedString name str = name <> indent pad str
  where
  pad = 1 + 10 - length (unpackString name)

usageModifier : ∀ {ℓ} (name : String) (cs : Modifier ℓ name) → Printer
usageModifier name mod i = (indent i $ namedString name $ display mod) ∷ []
  where
  display : Modifier _ _ → String
  display (mkFlag   f) = lower $ `project "description" f
  display (mkOption o) = lower $ `project "description" o

usageModifiers : ∀ {ℓ} {names : USL} → Record names (toFields ℓ) → Printer
usageModifiers = foldrR (λ _ mod' p i → usageModifier _ mod' i <> p i) (const [])

mutual
  usageCommand : ∀ {ℓ i} (name : String) (r : Command ℓ name {i}) → Printer
  usageCommand name r i
    = indent i (namedString name $ description r)
      ∷ usageCommands (snd $ subcommands r) (2 + i)
      ++ usageModifiers (snd $ modifiers r) (2 + i)

  usageCommands : ∀ {ℓ i} {names : USL} (cs : Commands ℓ names {i}) → Printer
  usageCommands (commands mkRecord cs)
    = [foldrR] (λ _ c p i → usageCommand _ c i <> p i) (const []) cs
