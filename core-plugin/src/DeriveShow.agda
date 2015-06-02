module DeriveShow where

open import MyPrelude hiding (_$_; [_]; show)
open import TypedCore
open import HelloWorld


-- data Foo = Barry | Bar Bool

FooADT : ADT ∗
FooADT = makeADT (fcon "Data" "Foo")
                 ((fcon "Data" "Barry" , []) ∷ (fcon "Data" "Bar" , con `Bool` ∷ []) ∷ [])

`Foo` : TyCon ∗
`Foo` = con FooADT

`Barry` : DataCon `Foo`
`Barry` = con FooADT zero

`Bar` : DataCon `Foo`
`Bar` = con FooADT (suc zero)

`showFoo` : Expr [] [] (con `Foo` ⇒ `String`)
`showFoo` = lam (con `Foo`)
                (match FooADT [] (var hd)
                       (alt (con `Barry`) (str "Barry") ∷
                        alt (con `Bar`) (stringAppend $ (str "Bar ") $ show (var hd)) ∷ [])
                       refl)

-- showFoo :: Foo -> String
-- showFoo = \foo -> case foo of
--   Barry -> "Barry"
--   Bar b -> "Bar" ++ show b


intercalate : ∀ {Σ} {Γ : Cxt Σ} →
                Expr Σ Γ (forAll ∗ (con `List` $ tvar hd ⇒
                                    con `List` $ (con `List` $ tvar hd) ⇒
                                    con `List` $ tvar hd))
intercalate = fvar (fvar "Data.List" "intercalate")


mkList : ∀ {Σ} {Γ : Cxt Σ} {τ : Type Σ ∗} →
           List (Expr Σ Γ τ) →
           Expr Σ Γ (con `List` $ τ)
mkList = foldr (λ e es → con `Cons` [ _ ] $ e $ es ) (con `Nil` [ _ ])

-- TODO update
-- -- TODO ∀ κ + arguments
-- deriveShow : (tc : TyCon ∗) → Expr [] [] (con tc ⇒ `String`)
-- deriveShow tc {{ck}} = lam (con tc)
--                            (match (var hd)
--                                   (map makeBranch constructors)
--                                   refl)
--   where
--     makeBranch : DataCon tc → Branch [] (con tc ∷ []) (con tc) `String`
--     makeBranch dc = alt (con [] dc)
--                         (intercalate [ _ ] $ str " " $
--                          mkList (str (dataConName dc) ∷ []))



{-

TyCon.tyConDataCons :: TyCon -> [DataCon]



class Show a where
  show :: a -> String

instance Show Triple where
  show x = case x of
    Foo -> "Foo"
    Bar i -> "Bar" ++ " " ++ show i
-}
