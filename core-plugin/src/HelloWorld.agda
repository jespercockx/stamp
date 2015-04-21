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


charFDC : ForeignDataCon
charFDC = fcon "GHC.Base" "Char"

`Char` : TyCon ∗
`Char` = con (fcon "GHC.Base" "Char") (charFDC ∷ [])

charDC : DataCon `Char` -- TODO cheat
charDC = con charFDC `Char` hd (con `Char` ∷ []) -- TODO cheat

`String` : ∀ {Σ} → Type Σ ∗
`String` = con `List` $ con `Char`

`Unit` : ∀ {Σ} → Type Σ ∗
`Unit` = con (con (fcon "GHC.Base" "()") [])

`IO` : ∀ {Σ} → Type Σ (∗ ⇒ ∗)
`IO` = con (con (fcon "System.IO" "IO") [])

`putStrLn` : ∀ {Σ} {Γ : Cxt Σ} → Expr Σ Γ (`String` ⇒ `IO` $ `Unit`)
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


`Show` : ∀ {Σ} → Type Σ (∗ ⇒ ∗)
`Show` = con (con (fcon "GHC.Show" "Show") [])


`show` : ∀ {Σ} {Γ : Cxt Σ} → Expr Σ Γ (forAll ∗ ((`Show` $ tvar hd) ⇒ tvar hd ⇒ `String`))
`show` = fvar (fvar "GHC.Show" "show")



record ShowC {Σ} (τ : Type Σ ∗) : Set where
  field
    showDict : ∀ {Γ : Cxt Σ} → Expr Σ Γ (`Show` $ τ)

open ShowC {{...}} public



show : ∀ {Σ} {Γ : Cxt Σ} {τ : Type Σ ∗} {{dict : ShowC {Σ} τ}} →
         Expr Σ Γ τ → Expr Σ Γ `String`
show {τ = τ} e = `show` [ τ ] $ showDict $ e



instance
  `ShowBool` : ∀ {Σ} → ShowC {Σ} (con `Bool`)
  `ShowBool` = record { showDict = fdict fdict }

  `ShowChar` : ∀ {Σ} → ShowC {Σ} (con `Char`)
  `ShowChar` = record { showDict = fdict fdict }

printHelloWorld : Expr [] [] (`IO` $ `Unit`)
printHelloWorld = `putStrLn` $ (`++` [ con `Char` ] $ str "hello" $ show (con `True`))
-- printHelloWorld = `putStrLn` $ (`++` [ con `Char` ] $ show (char 'a') $ show (con `True`))
-- printHelloWorld = `putStrLn` $ (stringAppend $ str "hello " $ str "world")
-- printHelloWorld = `putStrLn` $ (`++` [ con `Char` ] $ str "hello " $ str "world")
