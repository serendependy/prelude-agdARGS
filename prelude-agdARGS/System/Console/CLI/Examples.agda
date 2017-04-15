module prelude-agdARGS.System.Console.CLI.Examples where

open import Prelude

open import prelude-agdARGS.Data.Record.Usual
open import prelude-agdARGS.Data.UniqueSortedList.Usual
open import prelude-agdARGS.System.Console.Options.Domain
open import prelude-agdARGS.System.Console.Options.Usual
open Args
open import prelude-agdARGS.System.Console.Modifiers
open import prelude-agdARGS.System.Console.CLI
open import prelude-agdARGS.System.Console.CLI.Usual
open import prelude-agdARGS.Algebra.Magma

git-exec : Command lzero "git"
git-exec = record
  { description = "A distributed revision control system with an emphasis on speed,\
                   \ data integrity, and support for distributed, non-linear workflows"
  ; subcommands = _ , < "add"   ∷= record (basic $ lotsOf filePath)
                          { description = "Add file contents to the index"}
                      ⟨ "clone" ∷= record (basic url)
                          { description = "Clone a repository into a new directory"}
                      ⟨ "push" ∷= git-push
                      ⟨ ⟨⟩
  ; modifiers   = noModifiers
  ; arguments   = lotsOf filePath
  }
  where
  git-push = record
    { description = "Update remote refs along with associated objects"
    ; subcommands = noSubCommands
    ; modifiers   = _ , "--force" ∷= flag $ "Usually, the command refuses to update a remote ref that\
                                        \ is not an ancestor of the local ref used to overwrite it. This\
                                        \ flag disables the check. This can cause the remote repository\
                                        \ to lose commits; use it with care."
                    ⟨ ⟨⟩
    ; arguments   = none
    }

git : CLI lzero
git = record { name = "git" ; exec = git-exec }
