module schanuel where

open import Agda.Primitive

import category as cat
import fin-mono as I
import presheaf as psh

-- TODO: define atomic sheaves!
-- cat : ..{ℓ : _} ..(ℓ′ : _) (𝒮 : Set ℓ) → cat.t (lsuc ℓ′ ⊔ ℓ) (ℓ′ ⊔ ℓ)
-- cat ℓ 𝒮 = sh.cat ℓ (I.cat 𝒮)
