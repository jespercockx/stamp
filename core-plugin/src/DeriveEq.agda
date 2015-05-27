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



`&&` : ∀ {Σ} {Γ : Cxt Σ} → Expr Σ Γ (con `Bool` ⇒ con `Bool` ⇒ con `Bool`)
`&&` = fvar (fvar "GHC.Base" "&&")


and : ∀ {Σ} {Γ : Cxt Σ} → List (Expr Σ Γ (con `Bool`)) → Expr Σ Γ (con `Bool`)
and [] = con `True`
and (b ∷ bools) = foldr (λ b₁ b₂ → `&&` $ b₁ $ b₂) b bools

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

firstBinder : ∀ {A : Set} {x y : A} {xs ys zs : List A} →
                x ∈ (xs +++ (x ∷ (ys ++ (xs +++ (y ∷ (ys ++ zs))))))
firstBinder {xs = xs} = ∈-+++-suffix {ys = xs} hd

secondBinder : ∀ {A : Set} {x y : A} {xs ys zs : List A} →
                 x ∈ (xs +++ (y ∷ (ys ++ (xs +++ (x ∷ (ys ++ zs))))))
secondBinder {_} {x} {_} {xs} {ys} {zs}
  = ∈-+++-suffix {ys = xs}
    (tl (∈-++-suffix {ys = ys} (∈-+++-suffix {ys = xs} hd)))


deriveEq : (tc : TyCon ∗) {{ck : ConstructorsKnown tc}} →
           Expr [] [] (con tc ⇒ con tc ⇒ con `Bool`)
deriveEq tc = lam (con tc) (lam (con tc)
              (match (var (tl hd))
                     (map makeBranch constructors)
                     refl))
  where
    makeBranch : (dc : DataCon tc) →
                 Branch [] (con tc ∷ con tc ∷ []) (con tc) (con `Bool`)
    makeBranch dc
      = alt (con [] dc)
            (match (var (∈-+++-suffix {ys = patBinders (con [] dc)} hd))
                   (map (makeNestedBranch dc) constructors) refl)

      where
        makeNestedBranch : ∀ {tc} → (dc dc′ : DataCon tc) →
                           Branch [] (patBinders (con [] dc) +++
                                      con tc ∷ con tc ∷ [])
                                     (con tc) (con `Bool`)
        makeNestedBranch dc dc′ with dc == dc′
        ... | no ¬eq = alt (con [] dc′) (con `False`)
        ... | yes eq = alt (con [] dc)
                           (compareArgs (patBinders (con [] dc)) {τs = []})
          where
            compareArgs : ∀ {tc : TyCon ∗} →
                            (binders : Cxt [])
                            {τs : List (Type [] ∗)} →
                            Expr [] (binders +++ (τs ++ binders +++
                                     (τs ++ con tc ∷ con tc ∷ [])))
                                    (con `Bool`)
            compareArgs [] = con `True`
            compareArgs {tc} (τ ∷ binders) {τs}
              = `&&` $ (`==` [ τ ] $
                        {!!} $
                        var (firstBinder {xs = binders} {ys = τs}) $
                        var (secondBinder {xs = binders} {ys = τs}))
                     $ compareArgs {tc} binders {τs = τ ∷ τs}
