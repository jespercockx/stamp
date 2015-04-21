module DeriveShow where

open import MyPrelude hiding (_$_; [_]; show)
open import TypedCore
open import HelloWorld


-- data Foo = Barry | Bar Bool

BarryDC : ForeignDataCon
BarryDC = fcon "Data" "Barry"

BarDC : ForeignDataCon
BarDC = fcon "Data" "Bar"

`Foo` : TyCon ∗
`Foo` = con (fcon "Data" "Foo") (BarryDC ∷ BarDC ∷ [])

`Barry` : DataCon `Foo`
`Barry` = con BarryDC `Foo` hd []

`Bar` : DataCon `Foo`
`Bar` = con BarDC `Foo` (tl hd) (con `Bool` ∷ [])

`showFoo` : Expr [] [] (con `Foo` ⇒ `String`)
`showFoo` = lam (con `Foo`)
                (match (var hd)
                (alt (con [] `Barry`) (str "Barry") ∷
                 alt (con [] `Bar`) (stringAppend $ (str "Bar ") $ show (var hd)) ∷ [])
                refl)

-- showFoo :: Foo -> String
-- showFoo = \foo -> case foo of
--   Barry -> "Barry"
--   Bar b -> "Bar" ++ show b



{-

TyCon.tyConDataCons :: TyCon -> [DataCon]



class Show a where
  show :: a -> String

instance Show Triple where
  show x = case x of
    Foo -> "Foo"
    Bar i -> "Bar" ++ " " ++ show i
-}
