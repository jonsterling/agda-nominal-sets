module nat where

data t : Set where
  ze : t
  su : t → t

{-# BUILTIN NATURAL t #-}
