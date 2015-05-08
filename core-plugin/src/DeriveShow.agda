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

record ConstructorsKnown {κ} (tc : TyCon κ) : Set where
  field
    constructors : List (DataCon tc)
    all : tyConConstructors tc ≡ map dataConForeignDataCon constructors

open ConstructorsKnown {{...}} public

instance
  FooConstructorsKnown : ConstructorsKnown `Foo`
  FooConstructorsKnown = record { constructors = `Barry` ∷ `Bar` ∷ []
                                ; all = refl }

  BoolConstructorsKnown : ConstructorsKnown `Bool`
  BoolConstructorsKnown = record { constructors = `False` ∷ `True` ∷ []
                                 ; all = refl }


intercalate : ∀ {Σ} {Γ : Cxt Σ} →
                Expr Σ Γ (forAll ∗ (con `List` $ tvar hd ⇒
                                    con `List` $ (con `List` $ tvar hd) ⇒
                                    con `List` $ tvar hd))
intercalate = fvar (fvar "Data.List" "intercalate")


mkList : ∀ {Σ} {Γ : Cxt Σ} {τ : Type Σ ∗} →
           List (Expr Σ Γ τ) →
           Expr Σ Γ (con `List` $ τ)
mkList = foldr (λ e es → con `Cons` [ _ ] $ e $ es ) (con `Nil` [ _ ])


-- TODO ∀ κ + arguments
deriveShow : (tc : TyCon ∗) {{ck : ConstructorsKnown tc}} →
             Expr [] [] (con tc ⇒ `String`)
deriveShow tc {{ck}} = lam (con tc)
                           (match (var hd)
                                  (map makeBranch constructors)
                                  refl)
  where
    makeBranch : DataCon tc → Branch [] (con tc ∷ []) (con tc) `String`
    makeBranch dc = alt (con [] dc)
                        (intercalate [ _ ] $ str " " $
                         mkList (str (dataConName dc) ∷ []))



{-

TyCon.tyConDataCons :: TyCon -> [DataCon]



class Show a where
  show :: a -> String

instance Show Triple where
  show x = case x of
    Foo -> "Foo"
    Bar i -> "Bar" ++ " " ++ show i
-}
