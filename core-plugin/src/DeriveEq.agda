module DeriveEq where

open import MyPrelude hiding (_$_; [_]; show)
open import TypedCore
open import HelloWorld
open import DeriveShow



tuple2DC : ForeignDataCon
tuple2DC = fcon "GHC.Types" "(,)"

`Tuple2` : TyCon (∗ ⇒ ∗ ⇒ ∗)
`Tuple2` = con (fcon "GHC.Base" "(,)") (tuple2DC ∷ [])

`tuple2` : DataCon `Tuple2`
`tuple2` = con tuple2DC `Tuple2` hd (tvar (tl hd) ∷ tvar hd ∷ [])

-- This can't work because of substTop
-- mkTuple2 : ∀ {τ₁ τ₂ : Type [] ∗} → Expr [] [] τ₁ → Expr [] [] τ₂ →
--              Expr [] [] (con `Tuple2` $ τ₁ $ τ₂)
-- mkTuple2 {τ₁ = τ₁} {τ₂ = τ₂} e₁ e₂ = con `tuple2` [ τ₁ ] [ τ₂ ] $ e₁ $ e₂


identityTDC : ForeignDataCon
identityTDC = tuple2DC

`IdentityT` : TyCon ((∗ ⇒ ∗) ⇒ ∗ ⇒ ∗)
`IdentityT` = con (fcon "GHC.Base" "(,)") (identityTDC ∷ [])

IdentityT : Type [] ((∗ ⇒ ∗) ⇒ ∗ ⇒ ∗)
IdentityT = con `IdentityT`

`identityT` : DataCon `IdentityT`
`identityT` = con identityTDC `IdentityT` hd ((tvar (tl hd) $ tvar hd) ∷ [])

imb : Expr [] [] (con `IdentityT` $ con `Maybe` $ con `Bool`)
imb = con `identityT` [ con `Maybe` ] [ con `Bool` ] $
      con `Nothing` [ con `Bool` ]


`Eq` : ∀ {Σ} → Type Σ (∗ ⇒ ∗)
`Eq` = con (con (fcon "GHC.Base" "Eq") [])

`==` : ∀ {Σ} {Γ : Cxt Σ} → Expr Σ Γ (forAll ∗ ((`Eq` $ tvar hd) ⇒ tvar hd ⇒ tvar hd ⇒ con `Bool`))
`==` = fvar (fvar "GHC.Base" "==")


record EqC {Σ} (τ : Type Σ ∗) : Set where
  field
    eqDict : ∀ {Γ : Cxt Σ} → Expr Σ Γ (`Eq` $ τ)

open EqC {{...}} public

`eq` : ∀ {Σ} {Γ : Cxt Σ} {τ : Type Σ ∗} {{dict : EqC {Σ} τ}} →
         Expr Σ Γ τ → Expr Σ Γ τ → Expr Σ Γ (con `Bool`)
`eq` {τ = τ} e₁ e₂ = `==` [ τ ] $ eqDict $ e₁ $ e₂

instance
  `EqBool` : ∀ {Σ} → EqC {Σ} (con `Bool`)
  `EqBool` = record { eqDict = fdict fdict }

  `EqChar` : ∀ {Σ} → EqC {Σ} (con `Char`)
  `EqChar` = record { eqDict = fdict fdict }


`eqFoo` : Expr [] [] (con `Foo` ⇒ con `Foo` ⇒  con `Bool`)
`eqFoo` = lam (con `Foo`) (lam (con `Foo`)
              (match (var (tl hd))
                     (alt (con [] `Barry`)
                          (match (var hd)
                          (alt (con [] `Barry`) (con `True`) ∷
                            alt (con [] `Bar`) (con `False`) ∷ []) refl) ∷
                      alt (con [] `Bar`)
                          (match (var (tl hd))
                          (alt (con [] `Barry`) (con `False`) ∷
                          alt (con [] `Bar`) (`eq` (var (tl hd)) (var hd)) ∷ [])
                          refl)
                      ∷ []) refl))

deriveEq : (tc : TyCon ∗) {{ck : ConstructorsKnown tc}} →
           Expr [] [] (con tc ⇒ con tc ⇒ con `Bool`)
deriveEq tc = lam (con tc) (lam (con tc)
              (match (var (tl hd))
                     (map makeBranch constructors)
                     refl))
  where
    makeBranch : DataCon tc → Branch [] (con tc ∷ con tc ∷ []) (con tc) (con `Bool`)
    makeBranch dc = alt (con [] dc) {!!}
