module prelude-agdARGS.System.Console.Modifiers where

open import Prelude

open import prelude-agdARGS.Level
open import prelude-agdARGS.Function
open import prelude-agdARGS.Algebra.Monoid
open import prelude-agdARGS.Data.String
open import prelude-agdARGS.Data.Error as Error
open import prelude-agdARGS.Data.Record.Usual as RU public
open Membership
open import prelude-agdARGS.System.Console.Options.Domain

Flag : ∀ ℓ → Fields (lsuc ℓ) _
Flag ℓ = Type $ "description" ∷= Lift String ⟨ ⟨⟩

Option : ∀ ℓ → Fields (lsuc ℓ) _
Option ℓ = Type $ "description" ∷= Lift String
                  ⟨ "arguments" ∷= Σ (Domain ℓ) (λ d → Parser d)
                  ⟨ ⟨⟩

data Modifier (ℓ : Level) (name : String) : Set (lsuc ℓ) where
  mkFlag   : Record _ (Flag ℓ)   → Modifier ℓ name
  mkOption : Record _ (Option ℓ) → Modifier ℓ name

flag : ∀ {ℓ} {name} → String → Modifier ℓ name
flag str = mkFlag ("description" ∷= lift str ⟨ ⟨⟩)

option : ∀ {ℓ name} → String → Σ (Domain ℓ) (λ d → Parser d) → Modifier ℓ name
option n p = mkOption $ "description" ∷= lift n
                      ⟨ "arguments"   ∷= p
                      ⟨ ⟨⟩

toFields : ∀ ℓ {lb ub} {names : UniqueSortedList lb ub} → Fields (lsuc ℓ) names
toFields ℓ = tabulateR $ λ {s} → const (Modifier ℓ s)

Modifiers : ∀ ℓ → Set (lsuc ℓ)
Modifiers ℓ = Σ USL (λ names → Record names (toFields ℓ))

noModifiers : ∀ {ℓ} → Modifiers ℓ
noModifiers = _ , ⟨⟩

ParsedModifier : {ℓ : Level} {name : String} → Modifier ℓ name → Set ℓ
ParsedModifier (mkFlag f)   = Lift Bool
ParsedModifier (mkOption o) = Maybe (Carrier $ fst $ `project "arguments" o)

ParsedModifiers : ∀ {ℓ} {names : USL} (mods : Record names (toFields ℓ)) → Set ℓ
ParsedModifiers {names = names} mods =
  Record names (Type $ RU.mapR (const ParsedModifier) mods)

updateModifier :
  {ℓ : Level} {names : USL} {mods : Record names (toFields ℓ)} (ps : ParsedModifiers mods) →
  {name : String} (pr : name ∈ names) (p : ParsedModifier (project′ pr mods)) →
  Error (ParsedModifiers mods)
updateModifier {ℓ} ps pr p = mkRecord <$> go (content ps) pr p

  where

  go : ∀ {lb ub} {names : UniqueSortedList lb ub} {mods : Record names (toFields ℓ)}
       → let fs = fields $ (Type $ RU.mapR (const ParsedModifier) mods)
         in (ps : [Record] names fs) {name : String} (pr : name ∈ names) (p : ParsedModifier (project′ pr mods))
         → Error $ [Record] names fs
  go {mods = mkRecord (mkFlag _   , _)} (q       , ps)        zero p
    = pure (p , ps)
  go {mods = mkRecord (mkOption _ , _)} (nothing , ps)        zero p
    = pure (p , ps)
  go {mods = mkRecord (mkOption o , _)} (just q  , ps) {name} zero p
    = (_, ps) <$>
      let dom = (fst $ `project "arguments" o)
      in (case_return_of_
           dom (λ d → Maybe (Carrier d) → Carrier d → Error $ Maybe $ Carrier d)
               (λ { (Some _) → λ _ _ → throw $ concatList $ "MkOption " ∷ name ∷ " set twice" ∷ []
                  ; (ALot M) → λ p q → pure $ p <> just q})
         ) p q
  go {mods = mkRecord (_ , _)} (q , ps) (succ pr) p = (λ ps → q , ps) <$> go ps pr p

