module fin-mono where

import list
import category as cat

_↪_ : {ℓ : _} {𝒮 : Set ℓ} → list.t 𝒮 → list.t 𝒮 → Set ℓ
xs ↪ ys = {x : _} → x list.∈ xs → x list.∈ ys

{-
cat : {ℓ : _} (𝒮 : Set ℓ) → cat.t ℓ ℓ
cat.obj (cat 𝒮) = list.t 𝒮
cat.hom (cat 𝒮) = _↪_
cat.idn (cat 𝒮) i = i
cat.cmp (cat 𝒮) f g = λ i → f (g i)

-}
