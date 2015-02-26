module HelloWorld where

open import MyPrelude hiding (_≤_; _<_; _$_)
open import TypedCore
open import UntypedCore using (∗; _⇒_)
open import CoreSyn
  using (mkMachString; charTyCon; listTyCon; unitTyCon; tcNameSpace; varNameSpace)



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

-- -- IO ∷ () ∷ String
-- helloWorld : Expr ((∗ ⇒ ∗) ∷ ∗ ∷ ∗ ∷ []) (({!!} ⇒ {!!}) ∷ []) (var hd $ var (tl hd))
-- helloWorld = var hd $ lit (mkMachString "Hello world")

helloWorld : Expr [] [] `String`
helloWorld = lit (lit (mkMachString "Hello World"))

printHelloWorld : Expr [] [] (`IO` $ `Unit`)
printHelloWorld = `putStrLn` $ helloWorld

-- CONTINUE: see error
