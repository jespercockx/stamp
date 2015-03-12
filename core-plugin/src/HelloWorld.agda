module HelloWorld where

open import MyPrelude hiding (_≤_; _<_; _$_; [_]; Show; show)
open import TypedCore
open import CoreSyn
  using (DataCon; mkMachChar; mkMachString; charTyCon;
         listTyCon; unitTyCon; boolTyCon;
         tcNameSpace; varNameSpace; dataNameSpace; clsNameSpace)

postulate
  `String#`    : ∀ {Σ} → Type Σ ∗
  trueDataCon : DataCon
  charDataCon : DataCon
{-# COMPILED trueDataCon GhcPlugins.trueDataCon #-}
{-# COMPILED charDataCon GhcPlugins.charDataCon #-}
-- TODO add boxed kind?

`Char` : ∀ {Σ} → Type Σ ∗
`Char` = foreign (con charTyCon)

`List` : ∀ {Σ} → Type Σ (∗ ⇒ ∗)
`List` = foreign (con listTyCon)

`String` : ∀ {Σ} → Type Σ ∗
`String` = `List` $ `Char`

`Unit` : ∀ {Σ} → Type Σ ∗
`Unit` = foreign (con unitTyCon)

`IO` : ∀ {Σ} → Type Σ (∗ ⇒ ∗)
`IO` = foreign (var tcNameSpace "System.IO" "IO")

`putStrLn` : ∀ {Σ} {Γ : Cxt Σ} → Expr Σ Γ (`String` ⇒ `IO` $ `Unit`)
`putStrLn` = foreign (var varNameSpace "System.IO" "putStrLn")

`unpackCStringUtf8#` : ∀ {Σ} {Γ : Cxt Σ} → Expr Σ Γ (`String` ⇒ `String`)
`unpackCStringUtf8#` = foreign (var varNameSpace "GHC.CString" "unpackCStringUtf8#")
-- TODO maybe a smart constructor? -> Smart constructors for all
-- literals. Can we do this without losing type-safety by
-- construction?

char : Char → Expr [] [] `Char`
char c = foreign (con charDataCon) $ foreign l
  where
    l : ForeignExpr [] `Char`
    l = lit (mkMachChar c)

str : String → Expr [] [] `String`
str s = `unpackCStringUtf8#` $ foreign (lit (mkMachString s))

`++` : ∀ {Σ} {Γ : Cxt Σ} → Expr Σ Γ (forAll ∗ (`List` $ var hd ⇒ `List` $ var hd ⇒ `List` $ var hd))
`++` = foreign (var varNameSpace "Data.List" "++")

stringConcat : ∀ {Σ} {Γ : Cxt Σ} → Expr Σ Γ (`String` ⇒ `String` ⇒ `String`)
stringConcat = lam `String` (lam `String` (`++` [ `Char` ] $ var (tl hd) $ var hd))


`Bool` : ∀ {Σ} → Type Σ ∗
`Bool` = foreign (con boolTyCon)

`True` : ∀ {Σ} {Γ : Cxt Σ} → Expr Σ Γ `Bool`
`True` = foreign (con trueDataCon)

`Show` : ∀ {Σ} → Type Σ (∗ ⇒ ∗)
`Show` = foreign (var clsNameSpace "GHC.Show" "Show")

`show` : ∀ {Σ} {Γ : Cxt Σ} → Expr Σ Γ (forAll ∗ ((`Show` $ var hd) ⇒ var hd ⇒ `String`))
`show` = foreign (var varNameSpace "GHC.Show" "show")

-- TODO use Agda's records/instance search for type-class evidence
record ShowC {Σ} (τ : Type Σ ∗) : Set where
  field
    showDict : ∀ {Γ : Cxt Σ} → Expr Σ Γ (`Show` $ τ)

open ShowC {{...}} public


show : ∀ {Σ} {Γ : Cxt Σ} {τ : Type Σ ∗} {{dict : ShowC {Σ} τ}} →
         Expr Σ Γ τ → Expr Σ Γ `String`
show {τ = τ} e = `show` [ τ ] $ showDict $ e


instance
  `ShowBool` : ∀ {Σ} → ShowC {Σ} `Bool`
  `ShowBool` = record { showDict = foreign dict }

  `ShowChar` : ∀ {Σ} → ShowC {Σ} `Char`
  `ShowChar` = record { showDict = foreign dict }

printHelloWorld : Expr [] [] (`IO` $ `Unit`)
printHelloWorld = `putStrLn` $ (`++` [ `Char` ] $ show (char 'a') $ show `True`)
-- printHelloWorld = `putStrLn` $ (stringConcat $ str "hello " $ str "world")
-- printHelloWorld = `putStrLn` $ (`++` [ `Char` ] $ str "hello " $ str "world")
