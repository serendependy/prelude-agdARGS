open import Prelude

open import prelude-agdARGS.Level
open import prelude-agdARGS.Data.Infinities
open import prelude-agdARGS.Relation.Binary

module prelude-agdARGS.Data.Record
  {a e l : Level} {A : Set a} ⦃ STO : StrictTotalOrder {e = e} {l} A ⦄ where

-- A Record is characterised by a set of field names. We decide
-- to represent this set by a UniqueSortedList in order to ensure
-- unicity of field names. Hence the following import:

open import prelude-agdARGS.Data.UniqueSortedList A ⦃ STO ⦄ as UniqueSortedList
open UniqueSortedList.Membership
open import prelude-agdARGS.Data.UniqueSortedList.SmartConstructors ⦃ STO ⦄ as SC
  hiding (module MayFail ; module NeverFail)

-- We then need to define what the content of each one of these
-- fields is. This is taken care of by associating a set to each
-- index of the UniqueSortedList of field names.

[Fields] : ∀ ℓ {lb ub} → (args : UniqueSortedList lb ub) → Set (lsuc ℓ)
[Fields] ℓ (_ ■) = Lift Unit
[Fields] ℓ (_ ,' _ ∷ args) = Set ℓ × [Fields] ℓ args

record Fields (ℓ : Level) {lb ub : _} (args : UniqueSortedList lb ub) : Set (lsuc ℓ) where
  constructor mkFields
  field
    fields : [Fields] ℓ args
open Fields public

-- We expect to be able to lookup a field's type from a Fields definition
[lookupR] : ∀ {ℓ} {lb ub} {args : UniqueSortedList lb ub} {arg : _}
           → (pr : arg ∈ args) → (fs : [Fields] ℓ args)
           → Set ℓ
[lookupR] zero (f , _) = f
[lookupR] (succ pr) (_ , fs) = [lookupR] pr fs

lookupR : ∀ {ℓ} {lb ub} {args : UniqueSortedList lb ub} {arg : _}
         → (pr : arg ∈ args) (fs : Fields ℓ args) → Set ℓ
lookupR pr = [lookupR] pr ∘ fields

-- We may tabulate a function associating, to each element, a Set in order
-- to get a Fields. Cue the simplest examples: constant Set ℓ.

[tabulateR] : ∀ {ℓ} {lb ub}
              → (args : UniqueSortedList lb ub) (ρ : {arg : _} (pr : arg ∈ args) → Set ℓ)
              → [Fields] ℓ args
[tabulateR] (_ ■) ρ = lift tt
[tabulateR] (arg ,' _ ∷ args) ρ = ρ zero , [tabulateR] args (ρ ∘ succ)

tabulateR : ∀ {ℓ} {lb ub} {args : UniqueSortedList lb ub}
            → (ρ : {arg : _} (pr : arg ∈ args) → Set ℓ)
            → Fields ℓ args
tabulateR {args = args} = mkFields ∘ [tabulateR] args

[Sets] : ∀ ℓ {lb ub : _}
         → (args : UniqueSortedList lb ub)
         → [Fields] (lsuc ℓ) args
[Sets] ℓ args = [tabulateR] args $ const $ Set ℓ

Sets : ∀ ℓ {lb ub : _} {args : UniqueSortedList lb ub}
       → Fields (lsuc ℓ) args
Sets ℓ = tabulateR $ const $ Set ℓ

-- We can apply a set transformer to each one the elements. This will
-- be useful later on when dealing with records whose elements are
-- in an applicative functor or a monad

[_[_]] : ∀ {ℓ} {lb ub : _} {args : UniqueSortedList lb ub}
         → (a : Set ℓ → Set ℓ) → [Fields] ℓ args
         → [Fields] ℓ args
[_[_]] {args = lt ■}           a f = f
[_[_]] {args = hd ,' _ ∷ args} a (f , fs) = (a f) , [ a [ fs ]]

infix 5 _[_]
_[_] : ∀ {ℓ} {lb ub : _} {args : UniqueSortedList lb ub}
       → (a : Set ℓ → Set ℓ) → Fields ℓ args
       → Fields ℓ args
a [ f ] = mkFields [ a [ fields f ]]

-- A record is then defined by aggregating an element of each one
-- of these sets in a right-nested tuple.

[Record] : ∀ {ℓ} {lb ub}
           → (args : UniqueSortedList lb ub) → (f : [Fields] ℓ args)
           → Set ℓ
[Record] (_ ■) f = Lift Unit
[Record] (_ ,' _ ∷ args) (f , fs) = f × [Record] args fs

record Record {ℓ lb ub} (args : UniqueSortedList lb ub) (f : Fields ℓ args) : Set ℓ where
  constructor mkRecord
  field
    content : [Record] args (fields f)
open Record public

module NeverFail where
  open SC.NeverFail

  -- We may also insert a new field
  [Finsert] : ∀ {ℓ} {lb ub} {args : UniqueSortedList lb ub} arg lt₁ lt₂
              → Set ℓ → [Fields] ℓ args
              → [Fields] ℓ (insertUSL′ arg lt₁ lt₂ args)
  [Finsert] {args = _ ■}            arg lt₁ lt₂ S f = S , _
  [Finsert] {args = hd ,' _ ∷ args} arg lt₁ lt₂ S f
    with stcompare arg hd
  ... | less _
    = S , f
  ... | equal _
    = S , snd f
  ... | greater gt
    = fst f , [Finsert] arg (↑ gt) lt₂ S (snd f)

  Finsert : ∀ {ℓ} {lb ub} {args : UniqueSortedList lb ub} arg lt₁ lt₂
            → Set ℓ → Fields ℓ args
            → Fields ℓ (insertUSL′ arg lt₁ lt₂ args)
  Finsert arg lt₁ lt₂ S (mkFields f) = mkFields ([Finsert] arg lt₁ lt₂ S f)

  [Rinsert] : ∀ {ℓ} {lb ub} {args : UniqueSortedList lb ub}
                {f : [Fields] ℓ args} arg lt₁ lt₂ {S : Set ℓ}
              → (v : S) → [Record] args f → [Record] _ ([Finsert] arg lt₁ lt₂ S f)
  [Rinsert] {args = _ ■} arg lt₁ lt₂ v f = v , _
  [Rinsert] {args = hd ,' lt ∷ args} {S , Fs} arg lt₁ lt₂ v f
    with stcompare arg hd
  ... | less _′
    = v , f
  ... | equal _
    =  v , snd f
  ... | greater gt
    = fst f , [Rinsert] arg (↑ gt) lt₂ v (snd f)

  Rinsert : ∀ {ℓ} {ub lb} {args : UniqueSortedList lb ub} {f : Fields ℓ args} arg lt₁ lt₂
            → {S : Set ℓ} (v : S) → Record args f
            → Record _ (Finsert arg lt₁ lt₂ S f)
  Rinsert arg lt₁ lt₂ v (mkRecord r) = mkRecord ([Rinsert] arg lt₁ lt₂ v r)

[foldrR] : ∀ {ℓ ℓ′ lb ub} {names : UniqueSortedList lb ub} {A : Set ℓ′} {f : ∀ {n} (pr : n ∈ names) → Set ℓ} →
          (∀ {n} pr → f {n} pr → A → A) → A → [Record] names ([tabulateR] names f) → A
[foldrR] {names = lt ■}            c n r       = n
[foldrR] {names = hd ,' lt ∷ names} c n (v , r) = c zero v $ [foldrR] (c ∘ succ) n r

foldrR : ∀ {ℓ ℓ′ lb ub} {names : UniqueSortedList lb ub}  {A : Set ℓ′} {f : ∀ {n} (pr : n ∈ names) → Set ℓ} →
         (∀ {n} pr → f {n} pr → A → A) → A → Record names (tabulateR f) → A
foldrR c n = [foldrR] c n ∘ content

[MRecord] : ∀ {ℓ lb ub} (args : UniqueSortedList lb ub) (f : [Fields] ℓ args) → Set ℓ
[MRecord] (lt ■)           f        = Lift ⊤
[MRecord] (hd ,' lt ∷ args) (f , fs) = Maybe f × [MRecord] args fs

record MRecord {ℓ lb ub} (args : UniqueSortedList lb ub) (f : Fields ℓ args) : Set ℓ where
  constructor mkMRecord
  field
    mcontent : [MRecord] args (fields f)
open MRecord public

-- The first thing we expect Records to deliver is the ability to
-- project the content of a field given its name.

[project] : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} {fs : [Fields] ℓ args}
            {arg : _} (pr : arg ∈ args) → [Record] args fs → [lookupR] pr fs
[project] {fs = _ , _} zero      (v , _) = v
[project] {fs = _ , _} (succ pr) (_ , r) = [project] pr r

project : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} {fs : Fields ℓ args}
          {arg : _} (pr : arg ∈ args) → Record args fs → lookupR pr fs
project pr = [project] pr ∘ content

[project′] : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub}
             {fs : {arg : _} (pr : arg ∈ args) → Set ℓ}
             {arg : _} (pr : arg ∈ args) → [Record] args ([tabulateR] args fs) → fs pr
[project′] zero     (v , _) = v
[project′] (succ pr) (_ , r) = [project′] pr r

project′ : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub}
           {fs : {arg : _} (pr : arg ∈ args) → Set ℓ}
           {arg : _} (pr : arg ∈ args) → Record args (tabulateR fs) → fs pr
project′ pr = [project′] pr ∘ content

-- A record of Sets can naturally be turned into the appropriate Fields
-- This is how we end up typing records with records

[Type] : {ℓ : Level} {lb ub : _} (args : UniqueSortedList lb ub)
         (r : [Record] args ([Sets] ℓ args)) → [Fields] ℓ args
[Type] (_ ■)           _       = lift tt
[Type] (_ ,' _ ∷ args) (v , r) = v , [Type] args r

Type : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub}
       (r : Record args (Sets ℓ)) → Fields ℓ args
Type = mkFields ∘ [Type] _ ∘ content

-- If we know how to populate fields, we naturally want to be able
-- to build a record by tabulating the defining function.

[pureR] : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} {fs : [Fields] ℓ args}
          (v : (arg : _) (pr : arg ∈ args) → [lookupR] pr fs) → [Record] args fs
[pureR] {args = lt ■}            {fs = _ }    v = lift tt
[pureR] {args = hd ,' lt ∷ args} {fs = _ , _} v = v _ zero , [pureR] (λ a → v a ∘ succ)

pureR : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} {fs : Fields ℓ args}
        (v : (arg : _) (pr : arg ∈ args) → lookupR pr fs) → Record args fs
pureR = mkRecord ∘ [pureR]

[pureR′] : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} {fs : {arg : _} (pr : arg ∈ args) → Set ℓ}
           (v : (arg : _) (pr : arg ∈ args) → fs pr) → [Record] args ([tabulateR] args fs)
[pureR′] {args = lt ■}           v = lift tt
[pureR′] {args = hd ,' lt ∷ args} v = v _ zero , [pureR′] (λ a → v a ∘ succ)

pureR′ : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} {fs : {arg : _} (pr : arg ∈ args) → Set ℓ}
         (v : (arg : _) (pr : arg ∈ args) → fs pr) → Record args (tabulateR fs)
pureR′ = mkRecord ∘ [pureR′]

-- A special sort of content may be a Fields-morphism: for each
-- field we will explaing how to turn data belonging to the first
-- type of Records to the second one.

infixr 3 _[⟶]_ _⟶_
_[⟶]_ : {ℓᶠ ℓᵍ : Level} {lb ub : _} {args : UniqueSortedList lb ub}
         (fs : [Fields] ℓᶠ args) (gs : [Fields] ℓᵍ args) → [Fields] (ℓᶠ ⊔ ℓᵍ) args
fs [⟶] gs = [tabulateR] _ $ λ pr → [lookupR] pr fs → [lookupR] pr gs

_⟶_ : {ℓᶠ ℓᵍ : Level} {lb ub : _} {args : UniqueSortedList lb ub}
       (f : Fields ℓᶠ args) (g : Fields ℓᵍ args) → Fields (ℓᶠ ⊔ ℓᵍ) args
fs ⟶ gs = mkFields $ fields fs [⟶] fields gs

-- And given a first record whose fields are Fields-morphism
-- and a second record whose fields are of the corresponding
-- domain, we can apply them in a pointwise manner:

[app] : {ℓᶠ ℓᵍ : Level} {lb ub : _} {args : UniqueSortedList lb ub}
        {fs : [Fields] ℓᶠ args} {gs : [Fields] ℓᵍ args}
        (fs→gs : [Record] args (fs [⟶] gs)) (r : [Record] args fs) → [Record] args gs
[app] {args = lt ■}             fs→gs         fs       = lift tt
[app] {args = hd ,' lt ∷ args}
      {fs = _ , _} {gs = _ , _} (f→g , fs→gs) (f , fs) = f→g f , [app] fs→gs fs

app : {ℓᶠ ℓᵍ : Level} {lb ub : _} {args : UniqueSortedList lb ub}
      {fs : Fields ℓᶠ args} {gs : Fields ℓᵍ args}
      (fs→gs : Record args (fs ⟶ gs)) (f : Record args fs) → Record args gs
app fs→gs f = mkRecord $ [app] (content fs→gs) (content f)

[mapR] : {ℓᶠ ℓᵍ : Level} {lb ub : _} (args : UniqueSortedList lb ub)
        {fs : {arg : _} (pr : arg ∈ args) → Set ℓᶠ}
        {gs : {arg : _} (pr : arg ∈ args) → Set ℓᵍ}
        (fs→gs : {arg : _} (pr : arg ∈ args) → fs pr → gs pr)
        (f : [Record] args ([tabulateR] args fs)) → [Record] args ([tabulateR] args gs)
[mapR] (_ ■)          fs→gs f       = lift tt
[mapR] (_ ,' _ ∷ args) fs→gs (v , f) = fs→gs zero v , [mapR] args (fs→gs ∘ succ) f

mapR : {ℓᶠ ℓᵍ : Level} {lb ub : _} {args : UniqueSortedList lb ub}
      {fs : {arg : _} (pr : arg ∈ args) → Set ℓᶠ}
      {gs : {arg : _} (pr : arg ∈ args) → Set ℓᵍ}
      (fs→gs : {arg : _} (pr : arg ∈ args) → fs pr → gs pr)
      (f : Record args (tabulateR fs)) → Record args (tabulateR gs)
mapR fs→gs = mkRecord ∘ [mapR] _ fs→gs ∘ content

[seqA] : ∀ {ℓ} {lb ub} {args : UniqueSortedList lb ub} {fs : [Fields] ℓ args}
           {App : Set ℓ → Set ℓ} ⦃ _ : Applicative App ⦄
         → [Record] args [ App [ fs ]] → App ([Record] args fs)
[seqA] {ℓ} {args = args} {App = App} = go args
  where
    go : {lb ub : _} (args : UniqueSortedList lb ub) {fs : [Fields] ℓ args} →
         [Record] args [ App [ fs ]] → App ([Record] args fs)
    go (lt ■)                          r        = pure r
    go (hd ,' lt ∷ args) {fs = _ , _ } (av , r) = _,_ <$> av <*> go args r
           
