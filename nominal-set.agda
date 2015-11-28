module nominal-set where

open import Agda.Primitive

import category as cat
import fin-mono as I
import sheaf as sh

t : ..{ℓ : _} ..(ℓ′ : _) (𝒮 : Set ℓ) → Set (lsuc ℓ′ ⊔ ℓ)
t ℓ 𝒮 = sh.t ℓ (cat.op (I.cat 𝒮))
