module prelude-agdARGS.System.Console.CLI.Parser where

open import Prelude

open import prelude-agdARGS.Relation.Nullary
open import prelude-agdARGS.Data.Error
open import prelude-agdARGS.Data.UniqueSortedList.Usual
open import prelude-agdARGS.Data.Record.Usual
open import prelude-agdARGS.System.Console.CLI

mutual

  parseSubCommand : ∀ {ℓ s} (c : Command ℓ s) {x}
                    → List String → x ∈ fst (subcommands c)
                    → Error $ ParsedCommand c
  parseSubCommand (mkCommand _ (subs , commands cs) _ _) xs pr
    = fmap′ (λ s → subCommand pr s) (parseCommand (project′ pr cs) xs)

                                     
  parseCommand : ∀ {ℓ s} (c : Command ℓ s)
                 → List String
                 → Error $ ParsedCommand c
  parseCommand _ []
    = throw "Not enough arguments"
  parseCommand c@(mkCommand descr (subs , (commands cs)) (_ , _) (_ , _)) ("--" ∷ xs) -- = {!!}
    = fmap′ (theCommand dummy) (parseArguments (arguments c) xs nothing)
  parseCommand c@(mkCommand descr (subs , (commands cs)) (_ , _) (_ , _)) (x ∷ [])
    = let dummyPD = ok (theCommand dummy nothing)
      in dec (x ∈? fst (subcommands c)) (parseSubCommand c []) $ λ _
         → dec (x ∈? fst (modifiers c)) (parseModifier c dummyPD dummyPD) $
         const $ parseArgument c dummyPD x
  parseCommand c@(mkCommand descr (subs , (commands cs)) (_ , _) (_ , _)) (x ∷ y ∷ xs)
    = dec (x ∈? fst (subcommands c)) (parseSubCommand c (y ∷ xs)) $ λ _
      → let recyxs = parseCommand c (y ∷ xs)
            recxs  = parseCommand c xs
        in dec (x ∈? fst (modifiers c)) (parseModifier c recyxs recxs) $
           const $ parseArgument c recyxs x

parseInterface : ∀ {ℓ} (c : CLI ℓ) → List String → Error $ ParsedInterface c
parseInterface c = parseCommand (exec c)
