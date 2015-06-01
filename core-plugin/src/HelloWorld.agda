module HelloWorld where

open import MyPrelude hiding (_≤_; _<_; _$_; [_]; Show; show)
open import TypedCore
open import CoreSyn
  using (mkMachChar; mkMachString; charTyCon;
         listTyCon; unitTyCon; boolTyCon;
         tcNameSpace; varNameSpace; dataNameSpace; clsNameSpace)

postulate
  `String#` : ∀ {Σ} → Type Σ ∗
-- TODO add boxed kind?

{-# TERMINATING #-}
`Char` : TyCon ∗


CharADT : ADT ∗
CharADT = makeADT (fcon "GHC.Base" "Char")  -- TODO cheat
                  (((fcon "GHC.Base" "Char") , (con `Char`) ∷ []) ∷ [])

`Char` = con CharADT

charDC : DataCon `Char`
charDC = con CharADT zero

`String` : ∀ {Σ} → Type Σ ∗
`String` = con `List` $ con `Char`


UnitADT : ADT ∗
UnitADT = makeADT (fcon "GHC.Base" "()")
                  ((fcon "GHC.Base" "()" , []) ∷ [])

`Unit` : TyCon ∗
`Unit` = con UnitADT


IOADT : ADT (∗ ⇒ ∗)
IOADT = makeADT (fcon "System.IO" "IO") []

`IO` : TyCon (∗ ⇒ ∗)
`IO` = con IOADT

`putStrLn` : ∀ {Σ} {Γ : Cxt Σ} → Expr Σ Γ (`String` ⇒ con `IO` $ con `Unit`)
`putStrLn` = fvar (fvar "System.IO" "putStrLn")


`unpackCStringUtf8#` : ∀ {Σ} {Γ : Cxt Σ} → Expr Σ Γ (`String` ⇒ `String`)
`unpackCStringUtf8#` = fvar (fvar "GHC.CString" "unpackCStringUtf8#")
-- TODO maybe a smart constructor? -> Smart constructors for all
-- literals. Can we do this without losing type-safety by
-- construction?

-- TODO make this work again
-- char : Char → Expr [] [] (con `Char`)
-- char c = con charDC $ lit (flit (mkMachChar c))


str : ∀ {Σ} {Γ : Cxt Σ} → String → Expr Σ Γ `String`
str s = `unpackCStringUtf8#` $ lit (flit (mkMachString s))


`++` : ∀ {Σ} {Γ : Cxt Σ} → Expr Σ Γ (forAll ∗ (con `List` $ tvar hd ⇒ con `List` $ tvar hd ⇒ con `List` $ tvar hd))
`++` = fvar (fvar "Data.List" "++")


stringAppend : ∀ {Σ} {Γ : Cxt Σ} → Expr Σ Γ (`String` ⇒ `String` ⇒ `String`)
stringAppend = lam `String` (lam `String` (`++` [ con `Char` ] $ var (tl hd) $ var hd))

-- TODO ConstraintKind?
ShowADT : ADT (∗ ⇒ ∗)
ShowADT = makeADT (fcon "GHC.Show" "Show") []

`Show` : TyCon (∗ ⇒ ∗)
`Show` = con ShowADT

`show` : ∀ {Σ} {Γ : Cxt Σ} → Expr Σ Γ (forAll ∗ ((con `Show` $ tvar hd) ⇒ tvar hd ⇒ `String`))
`show` = fvar (fvar "GHC.Show" "show")



record ShowC {Σ} (τ : Type Σ ∗) : Set where
  field
    showDict : ∀ {Γ : Cxt Σ} → Expr Σ Γ (con `Show` $ τ)

open ShowC {{...}} public



show : ∀ {Σ} {Γ : Cxt Σ} {τ : Type Σ ∗} {{dict : ShowC {Σ} τ}} →
         Expr Σ Γ τ → Expr Σ Γ `String`
show {τ = τ} e = `show` [ τ ] $ showDict $ e



instance
  `ShowBool` : ∀ {Σ} → ShowC {Σ} (con `Bool`)
  `ShowBool` = record { showDict = fdict fdict }

  `ShowChar` : ∀ {Σ} → ShowC {Σ} (con `Char`)
  `ShowChar` = record { showDict = fdict fdict }

printHelloWorld : Expr [] [] (con `IO` $ con `Unit`)
printHelloWorld = `putStrLn` $ (`++` [ con `Char` ] $ str "hello" $ show (con `True`))
-- printHelloWorld = `putStrLn` $ (`++` [ con `Char` ] $ show (char 'a') $ show (con `True`))
-- printHelloWorld = `putStrLn` $ (stringAppend $ str "hello " $ str "world")
-- printHelloWorld = `putStrLn` $ (`++` [ con `Char` ] $ str "hello " $ str "world")
