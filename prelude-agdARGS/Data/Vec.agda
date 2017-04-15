module prelude-agdARGS.Data.Vec where

open import Prelude

vzipWith : ∀ {a b c} {n} {A : Set a} {B : Set b} {C : Set c}
          → (A → B → C) → Vec A n → Vec B n
          → Vec C n
vzipWith  _⊕_ xs ys = pure _⊕_ <*>′ xs <*>′ ys
