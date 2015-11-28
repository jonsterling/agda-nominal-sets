module identification where

open import Agda.Primitive

data t {ℓ} {A : Set ℓ} (M : A) : A → Set ℓ where
  idn : t M M

{-# BUILTIN EQUALITY t #-}
{-# BUILTIN REFL idn #-}
