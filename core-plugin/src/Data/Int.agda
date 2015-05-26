module Data.Int where

open import Prelude.Number
open import Prelude.Nat
open import Prelude.Unit

postulate
  Int   : Set
  i0    : Int
  isuc  : Int → Int
  _i+_ : Int → Int → Int


{-# COMPILED_TYPE Int Int #-}
{-# COMPILED i0 (0 :: Int) #-}
{-# COMPILED isuc succ #-}
{-# COMPILED _i+_ (+) #-}


instance
  NumberInt : Number Int
  NumberInt = record { Constraint = λ _ → ⊤ ; fromNat = from }
    where
      from : Nat → {{_ : ⊤}} → Int
      from zero = i0
      from (suc n) = isuc (from n)
