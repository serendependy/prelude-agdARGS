module prelude-agdARGS.Data.Error where

open import Prelude

Error : ∀ {ℓ} → Set ℓ → Set ℓ
Error = Either String

pattern error e = left e
pattern ok x    = right x

throw : ∀ {a} {A : Set a} → String → Error A
throw = left

infixr 0 _e>>=_
_e>>=_ : ∀ {a b} {A : Set a} {B : Set b} → Error A → (A → Error B) → Error B
error e e>>= f = error e
ok    x e>>= f = f x

instance
  Functor′Error : ∀ {a b} → Functor′ {a} {b} Error
  Functor′.fmap′ Functor′Error f (error e) = error e
  Functor′.fmap′ Functor′Error f (ok    x) = ok (f x)
