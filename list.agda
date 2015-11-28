module list where

import vec
import nat

record t {ℓ} (A : Set ℓ) : Set ℓ where
  constructor [_]
  field
    {len} : nat.t
    π : vec.t A len
open t public

module _ {ℓ} {A : Set ℓ} where
  [] : t A
  [] = [ vec.[] ]

  {-# DISPLAY [_] vec.[] = vec.[] #-}

  _∷_ : A → t A → t A
  x ∷ xs = [ x vec.∷ π xs ]

  _∈_ : A → t A → Set ℓ
  x ∈ xs = x vec.∈ (π xs)
