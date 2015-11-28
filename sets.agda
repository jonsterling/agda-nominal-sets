module sets where

open import Agda.Primitive
import category as cat

cat : ..(ℓ : _) → cat.t (lsuc ℓ) ℓ
cat.obj (cat ℓ) = Set ℓ
cat.hom (cat ℓ) A B = A → B
cat.idn (cat ℓ) x = x
cat.cmp (cat ℓ) f g x = f (g x)
