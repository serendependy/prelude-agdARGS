module prelude-agdARGS.System.Console.Options where

open import Prelude

open import prelude-agdARGS.Level
open import prelude-agdARGS.Function
open import prelude-agdARGS.Relation.Binary
open import prelude-agdARGS.Relation.Binary.On as On
open import prelude-agdARGS.System.Console.Options.Domain
open import prelude-agdARGS.Data.String

record Option (ℓ : Level) : Set (lsuc ℓ) where
  field
    name        : String
    description : String
    flag        : String
    optional    : Bool
    domain      : Domain ℓ
    parser      : Parser domain
open Option

instance
  StrictTotalOrderOption : ∀ {ℓ} → StrictTotalOrder (Option ℓ)
  StrictTotalOrderOption {ℓ} = On.strictTotalOrder flag it

module Options (ℓ : Level) where

  open import prelude-agdARGS.Data.Infinities
  open import prelude-agdARGS.Data.UniqueSortedList
    (Option ℓ) ⦃ StrictTotalOrderOption ⦄
    as UniqueSortedList public
  open UniqueSortedList.Membership public
  open import prelude-agdARGS.Data.Error

  Options : Set (lsuc ℓ)
  Options = UniqueSortedList -∞ +∞

  Mode : ∀ {lb ub} (args : UniqueSortedList lb ub) → Set (lsuc ℓ)
  Mode args = (arg : Option ℓ) (pr : arg ∈ args) → Set ℓ

  ModeS : ∀ {lb ub} {hd} {lt : lb s< (↑ hd)} {args : UniqueSortedList (↑ hd) ub}
          → Mode {lb} (hd ,' lt ∷ args)
          → Mode args
  ModeS m = λ arg → m arg ∘ succ

  values : ∀ {lb ub} (args : UniqueSortedList lb ub) (m : Mode args) → Set ℓ
  values (lt ■) m = Lift ⊤
  values (hd ,' lt ∷ args) m = m hd zero × values args (ModeS m)

  -- This is a trick to facilitate type inference: when `args` is
  -- instantiated, `values` will compute, making it impossible
  -- to reconstruct `args`'s value, but `Values` will stay stuck.
  -- This is why `get` uses `Values` (and takes `args` as an
  -- implicit argument) and `parse` produces it.

  data Values (args : Options) (m : Mode args) : Set ℓ where
    mkValues : values args m → Values args m

  getValues : ∀ {lb ub} {args : UniqueSortedList lb ub} {arg : Option ℓ}
              → (m : Mode args) (pr : arg ∈ args) → values args m
              → m arg pr
  getValues m zero = fst
  getValues m (succ pr) = getValues (ModeS m) pr ∘ snd

  SetDomain : Domain ℓ → Set ℓ
  SetDomain = Carrier

  MaybeMode : ∀ {lb ub} {args : UniqueSortedList lb ub} → Mode args
  MaybeMode = const ∘ Maybe ∘ SetDomain ∘ domain

  defaultValues : ∀ {lb ub} (args : UniqueSortedList lb ub) → values args MaybeMode
  defaultValues (lt ■) = lift tt
  defaultValues (hd ,' lt ∷ args) = nothing , defaultValues args

  open import prelude-agdARGS.Relation.Nullary

  findOption : (str : String) (args : Options)
               → Dec (Σ (Option ℓ) (λ arg → arg ∈ args × flag arg ≡ str ))
  findOption str = search _==_ flag str

  genericGet : {args : Options} {m : Mode args}
               → (str : String) (opts : Values args m)
               → dec (findOption str args)
                     (uncurry $ (λ arg → m arg ∘ fst))
                     (const $ Lift Unit)
  genericGet {args} {m} str (mkValues opts)
    with findOption str args
  ... | no  _
    = lift tt
  ... | yes (arg , pr , _)
    = getValues m pr opts

  module _ {M : Set ℓ → Set ℓ} ⦃ MM : Monad M ⦄ where

    mapMValues : ∀ {lb ub}
                 → (args : UniqueSortedList lb ub) {f g : Mode args}
                 → (upd : (arg : Option ℓ) (pr : arg ∈ args) → f arg pr → M (g arg pr))
                 → values args f
                 → M (values args g)
    mapMValues (lt ■)            upd opts
      = return opts
    mapMValues (hd ,' lt ∷ args) upd (v , opts)
      = upd hd zero v >>= λ w
        → mapMValues args (λ arg → upd arg ∘ succ) opts >>= λ ws
        → return (w , ws)

    updateMValues : ∀ {lb ub} {args : UniqueSortedList lb ub} {m : Mode args} {arg : Option ℓ}
                    → (pr : arg ∈ args) (f : m arg pr → M (m arg pr))
                    → values args m
                    → M (values args m)
    updateMValues {args = args} {m} {arg} pr f = mapMValues _ (upd m pr f)
      where
      upd : ∀ {lb ub} {args : UniqueSortedList lb ub} (m : Mode args) {arg : Option ℓ}
            → (pr : arg ∈ args) (upd : m arg pr → M (m arg pr))
              (arg : Option ℓ) (pr : arg ∈ args) → m arg pr
            → M (m arg pr)
      upd m zero       f arg zero       = f
      upd m zero       f arg (succ pr₂) = return
      upd m (succ pr₁) f arg zero       = return
      upd m (succ pr₁) f arg (succ pr₂) = upd (ModeS m) pr₁ f arg pr₂       

  open import prelude-agdARGS.Algebra.Magma

  set : {args : Options} {arg : Option ℓ} (pr : arg ∈ args) (v : SetDomain (domain arg))
        → values args MaybeMode
        → Error (values args MaybeMode)
  set {args} {arg} pr v vs
    = updateMValues pr
                    (λ mmode →
                      elimDomain {P = P}
                                 (PSome mmode) {!!} {!!})
                    vs
    where
    P : Domain ℓ → Set ℓ
    P = const (Error (MaybeMode arg pr)) -- SetDomain d → Maybe (SetDomain d) → Error (Maybe (SetDomain d))

    PSome : MaybeMode arg pr → (S : Set ℓ) → P (Some S)
    PSome new S
      = maybe (return {!!})
              (const $ throw $ "Option " <> flag arg <> " set more than once")
              new

    -- PSome : (S : Set ℓ) → P (Some S)
    -- PSome S new
    --   = maybe (throw ("Option " <> flag arg <> " used more than once"))
    --           (λ x → return (just x))

    -- PALot : {A : Set ℓ} ⦃ M : Magma A ⦄ → P (ALot M)
    -- PALot new = {!!}
