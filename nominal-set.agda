module nominal-set where

open import Agda.Primitive

import sheaf as Sh
import fin-mono as I
import Category as C

t : ..{ℓ : _} (𝒮 : Set ℓ) → Set _
t 𝒮 = Sh.t {ℓ₁ᵒ = lzero} {ℓ₁ʰ = lzero} (C.Op.g (I.cat 𝒮))
