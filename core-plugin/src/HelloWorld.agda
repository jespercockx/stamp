module HelloWorld where

open import MyPrelude hiding (_≤_; _<_; _$_; [_])
open import TypedCore
open import UntypedCore using (∗; _⇒_)
open import CoreSyn
  using (mkMachString; charTyCon; listTyCon; unitTyCon; tcNameSpace; varNameSpace)

postulate
 `String#` : ∀ {Σ} → Type Σ ∗
-- TODO add boxed kind?

`Char` : ∀ {Σ} → Type Σ ∗
`Char` = con (tyCon charTyCon)

`List` : ∀ {Σ} → Type Σ (∗ ⇒ ∗)
`List` = con (tyCon listTyCon)

`String` : ∀ {Σ} → Type Σ ∗
`String` = `List` $ `Char`

`Unit` : ∀ {Σ} → Type Σ ∗
`Unit` = con (tyCon unitTyCon)

`IO` : ∀ {Σ} → Type Σ (∗ ⇒ ∗)
`IO` = ffor tcNameSpace "System.IO" "IO"

`putStrLn` : ∀ {Σ} {Γ : Cxt Σ} → Expr Σ Γ (`String` ⇒ `IO` $ `Unit`)
`putStrLn` = ffor varNameSpace "System.IO" "putStrLn"

`unpackCStringUtf8#` : ∀ {Σ} {Γ : Cxt Σ} → Expr Σ Γ (`String` ⇒ `String`)
`unpackCStringUtf8#` = ffor varNameSpace "GHC.CString" "unpackCStringUtf8#"
-- TODO maybe a smart constructor? -> Smart constructors for all
-- literals. Can we do this without losing type-safety by
-- construction?

str : String → Expr [] [] `String`
str s = `unpackCStringUtf8#` $ lit (lit (mkMachString s))

`++` : ∀ {Σ} {Γ : Cxt Σ} → Expr Σ Γ (forAll ∗ (`List` $ var hd ⇒ `List` $ var hd ⇒ `List` $ var hd))
`++` = ffor varNameSpace "Data.List" "++"

stringConcat : ∀ {Σ} {Γ : Cxt Σ} → Expr Σ Γ (`String` ⇒ `String` ⇒ `String`)
stringConcat = lam `String` (lam `String` (`++` [ `Char` ] $ var (tl hd) $ var hd))


printHelloWorld : Expr [] [] (`IO` $ `Unit`)
printHelloWorld = `putStrLn` $ (stringConcat $ str "hello " $ str "world")
-- printHelloWorld = `putStrLn` $ (`++` [ `Char` ] $ str "hello " $ str "world")
