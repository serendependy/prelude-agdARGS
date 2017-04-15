module prelude-agdARGS.System.Console.CLI where

open import Prelude
open import Agda.Builtin.Size

open import prelude-agdARGS.Level
open import prelude-agdARGS.Algebra.Magma
open import prelude-agdARGS.Data.String

open import prelude-agdARGS.Data.UniqueSortedList.Usual
  as UU hiding (_,'_∷_)
open import prelude-agdARGS.Data.Record.Usual as RU

open import prelude-agdARGS.System.Console.Options.Domain
open import prelude-agdARGS.System.Console.Options.Usual
open import prelude-agdARGS.System.Console.Modifiers

ParsedArgument : ∀ {ℓ} → (p : Σ (Domain ℓ) (λ d → Parser d)) → Set ℓ
ParsedArgument (d , p) = Carrier d

ParsedArguments : ∀ {ℓ} → (p : Σ (Domain ℓ) (λ d → Parser d)) → Set ℓ
ParsedArguments (d , p) = Maybe $ Carrier d

-- infix 4 commands_
mutual

  record Command (ℓ : Level) (name : String) {i : Size} : Set (lsuc ℓ) where
    inductive
    constructor mkCommand
    field
      description : String
      subcommands : SubCommands ℓ {i}
      modifiers   : Modifiers ℓ
      arguments   : Arguments ℓ

  SubCommands : ∀ ℓ {i : Size} → Set (lsuc ℓ)
  SubCommands ℓ {i} = Σ _ (λ names → Commands ℓ names {i})

  data Commands (ℓ : Level) (names : USL) : {i : Size} → Set (lsuc ℓ) where
    commands_ : ∀ {i} → Record names (tabulateR (λ {s} _ → Command ℓ s {i})) → Commands ℓ names {↑ i}

noSubCommands : ∀ {ℓ} → SubCommands ℓ
noSubCommands = _ , (commands ⟨⟩)

infix 4 commandsSugar
commandsSugar : ∀ {ℓ names} → Record names _ → Commands ℓ names
commandsSugar = commands_

syntax commandsSugar t = < t

basic : ∀ {ℓ} {s} → Arguments ℓ → Command ℓ s
basic {s = str} args = mkCommand str noSubCommands (_ , ⟨⟩) args

record CLI (ℓ : Level) : Set (lsuc ℓ) where
  field
    name : String
    exec : Command ℓ name
open CLI public
open Command public

open import prelude-agdARGS.Data.Infinities
open import prelude-agdARGS.Data.Record.Properties ⦃ STO = StrictTotalOrderString ⦄
open Membership

mutual

  data ParsedCommand {ℓ s} : (c : Command ℓ s) → Set (lsuc ℓ) where
    theCommand : {descr : String}
                 {subs : Σ USL (λ names → Commands ℓ names)}
                 {modNames : USL} {mods : Record modNames (toFields ℓ)}
                 (parsedMods : ParsedModifiers mods)
                 {args : Σ (Domain ℓ) (λ d → Parser d)}
                 (parsedArgs : ParsedArguments args)
                 → ParsedCommand (mkCommand descr subs (modNames , mods) args)
    subCommand  : {descr : String}
                 {sub : String} {subs : USL} (pr : sub ∈ subs) {cs : Record subs _}
                 {mods : Σ USL (λ names → Record names (toFields ℓ))} →
                 (parsedSub : ParsedCommand (project′ pr cs))
                 {args : Σ (Domain ℓ) (λ d → Parser d)}
                 → ParsedCommand (mkCommand descr (subs , commands cs) mods args)

ParsedInterface : ∀ {ℓ} → CLI ℓ → Set (lsuc ℓ)
ParsedInterface i = ParsedCommand (exec i)

infix 1 [_
infix 3 _∷=_&_]
-- infix 2 _⟦_⟧∙_

pattern [_ p = p
pattern _∷=_&_] descr mods args = theCommand {descr} mods args
-- pattern subCommand'_[_]_ desc pr sub = subCommand {sub = desc} pr sub

open import prelude-agdARGS.Data.Error

updateArgument : ∀ {ℓ} (d : Domain ℓ) (p : Parser d) (ps : ParsedArguments (d , p))
                 → String
                 → Error $ ParsedArguments (d , p)
updateArgument (Some S) p (just _) _ = throw ("Too many arguments: only one expected")
updateArgument (Some S) p nothing x = just <$> p x
updateArgument (ALot M) p ps x = maybe just (λ p q → just (p ∙' q)) ps <$> p x
  where _∙'_ = Magma._∙_ M

parseArguments : ∀ {ℓ} (p : Σ (Domain ℓ) (λ d → Parser d))
                 → List String → ParsedArguments p
                 → Error $ ParsedArguments p
parseArguments p str dft = foldl (cons p) (right dft) str
  where
  cons : ∀ p → Error (ParsedArguments p) → String → Error $ ParsedArguments p
  cons _       (error e) _   = error e
  cons (d , p) (right nothing)  str = just <$> p str
  cons (Some S , _) (right (just _)) _    = error "Too many arguments: only one expected"
  cons (ALot M , p) (right (just v)) str =
    p str >>= λ w
    → return (just (v ∙' w))
    where
    _∙'_ = Magma._∙_ M

[dummy] : ∀ {ℓ} {lb ub} (args : UniqueSortedList lb ub)
          → (mods : Record args (tabulateR (λ {s} _ → Modifier ℓ s)))
          → [Record] args (fields $ Type $ mapR (const ParsedModifier) mods)
[dummy] (_ ■) m
  = lift tt
[dummy] (hd ,' lt ∷ args) (mkRecord (mkFlag _   , ms))
  = lift false , [dummy] args (mkRecord ms)
[dummy] (hd ,' lt ∷ args) (mkRecord (mkOption _ , ms))
  = nothing , [dummy] args (mkRecord ms)

dummy : ∀ {ℓ} {lb ub} {args : UniqueSortedList lb ub} {mods : Record args (toFields ℓ)}
        → Record args (Type $ RU.mapR (const ParsedModifier) mods)
dummy = mkRecord $ [dummy] _ _

parseModifier : ∀ {ℓ s} (c : Command ℓ s) {x : String}
                → (recyxs recxs : Error $ ParsedCommand c)
                → x ∈ fst (modifiers c)
                → Error $ ParsedCommand c
parseModifier (mkCommand descr (subs , (commands cs)) (lt ■ , mkRecord cont) (d , p)) recyxs recxs ()
parseModifier {ℓ} c@(mkCommand descr (subs , (commands cs)) mods@(hd ,' lt ∷ usl , mkRecord cont) args@(d , p′))
              {x} recyxs recxs pr
  = (case_return_of_ (project′ {fs = λ {s₁} _ → Modifier ℓ s₁} pr (snd mods))
                     (λ m → Error (ParsedModifier m))
                     (λ { (mkFlag   f) → return $ lift true
                        ; (mkOption o@(mkRecord cont')) → fmap just (snd (`project "arguments" o) x)}))
    e>>= λ p → recyxs e>>= λ rec
    → case rec of
        λ { (theCommand parsedMods parsedArgs) → fmap′ (λ m → theCommand m parsedArgs) (updateModifier parsedMods pr p)
          ; (subCommand _ _) → throw "Found an mkFlag for command XXX with subcommand YYY"}

parseArgument : ∀ {ℓ s} (c : Command ℓ s) → Error (ParsedCommand c)
                → String → Error $ ParsedCommand c
parseArgument (mkCommand descr (sub , (commands subs)) mods@(_ , _) (d , p)) recyxs x
    = recyxs e>>= λ rec
      → case rec of λ
        { (theCommand parsedMods parsedArgs) → fmap′ (theCommand parsedMods) (updateArgument d p parsedArgs x)
        ; (subCommand _ _) → throw "Found an argument for command XXX with subcommand YYY"}
