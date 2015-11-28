module fin-mono where

import list
import category as cat

module _ {ℓ} {𝒮 : Set ℓ} where
  _↪_ : list.t 𝒮 → list.t 𝒮 → Set ℓ
  xs ↪ ys = {x : 𝒮} → x list.∈ xs → x list.∈ ys

cat : {ℓ : _} (𝒮 : Set ℓ) → cat.t ℓ ℓ
cat.obj (cat 𝒮) = list.t 𝒮
cat.hom (cat 𝒮) = _↪_
cat.idn (cat 𝒮) i = i
cat.cmp (cat 𝒮) f g = λ i → f (g i)
