module Data.Int where

open import Prelude.Nat

postulate
  Int   : Set
  i0    : Int
  isuc  : Int → Int
  _i+_ : Int → Int → Int


{-# COMPILED_TYPE Int Int #-}
{-# COMPILED i0 (0 :: Int) #-}
{-# COMPILED isuc succ #-}
{-# COMPILED _i+_ (+) #-}


fromNat : Nat → Int
fromNat zero = i0
fromNat (suc n) = isuc (fromNat n)
