module prelude-agdARGS.Data.String where

open import Prelude
open import Prelude.Equality.Unsafe
open import Numeric.Nat.Properties
open import prelude-agdARGS.Relation.Binary
open import prelude-agdARGS.Data.List
open import prelude-agdARGS.Data.Ord

fromVec : ∀ {n} → Vec Char n → String
fromVec = packString ∘ vecToList

concatList : List String → String
concatList = foldr _&_ ""

concatVec : ∀ {n} → Vec String n → String
concatVec = vfoldr _&_ ""

unlines : List String → String
unlines = concatList ∘ intersperse "\n"

stringReplicate : Nat → Char → String
stringReplicate n = packString ∘ replicate n

stringLength : String → Nat
stringLength = length ∘ unpackString

lines : String → List String
lines = map packString ∘ breakAll isNewLine ∘ unpackString
  where
    isNewLine : Char → Bool
    isNewLine c = isYes (c == '\n')

-- I hope this is true...
packUnpack : ∀ xs → (unpackString ∘ packString $ xs) ≡ xs
packUnpack xs = unsafeEqual

instance
  StrictTotalOrderString : StrictTotalOrder String
  StrictTotalOrderString = OrdToSTO ⦃ OrdA = it ⦄ (λ {x} {y} {z} → <-trans' {x} {y} {z})
     where
       <-trans' : Transitive _<_
       <-trans' {x} {y} {z} x<y y<z
         with primStringToList x | primStringToList y | primStringToList z
       <-trans' {x} {y} {z} nil<cons (head< x₂)
         | .[] | .(_ ∷ _) | .(_ ∷ _)
         = nil<cons
       <-trans' {x} {y} {z} nil<cons (tail< y<z)
         | .[] | .(_ ∷ _) | .(_ ∷ _)
         = nil<cons
       <-trans' {x} {y} {z} (head< x<y) (head< y<z)
         | .(_ ∷ _) | .(_ ∷ _) | .(_ ∷ _)
         = head< (x<y ⟨<⟩ y<z)
       <-trans' {x} {y} {z} (head< x<y) (tail< ys<zs)
         | .(_ ∷ _) | .(_ ∷ _) | .(_ ∷ _)
         = head< x<y
       <-trans' {x} {y} {z} (tail< xs<ys) (head< y<z)
         | .(_ ∷ _) | .(_ ∷ _) | .(_ ∷ _)
         = head< y<z
       <-trans' {x} {y} {z} (tail< {xs = xs} {ys = ys} xs<ys) (tail< {ys = zs} ys<zs)
         | .(_ ∷ _) | .(_ ∷ _) | .(_ ∷ zs)
         rewrite sym (packUnpack xs)
         | sym (packUnpack ys)
         | sym (packUnpack zs)
         = tail< (<-trans' {packString xs} {packString ys} {packString zs} xs<ys ys<zs)
