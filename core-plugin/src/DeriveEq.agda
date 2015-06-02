module DeriveEq where

open import MyPrelude hiding (_$_; [_]; show)
open import TypedCore
open import HelloWorld
open import DeriveShow


`&&` : ∀ {Σ} {Γ : Cxt Σ} → Expr Σ Γ (con `Bool` ⇒ con `Bool` ⇒ con `Bool`)
`&&` = fvar (fvar "GHC.Base" "&&")


and : ∀ {Σ} {Γ : Cxt Σ} → List (Expr Σ Γ (con `Bool`)) → Expr Σ Γ (con `Bool`)
and [] = con `True`
and (b ∷ bools) = foldr (λ b₁ b₂ → `&&` $ b₁ $ b₂) b bools

`Eq` : TyCon (∗ ⇒ ∗)
`Eq` = con (makeADT (fcon "GHC.Base" "Eq") [])

`==` : ∀ {Σ} {Γ : Cxt Σ} → Expr Σ Γ (forAll ∗ ((con `Eq` $ tvar hd) ⇒ tvar hd ⇒ tvar hd ⇒ con `Bool`))
`==` = fvar (fvar "GHC.Base" "==")


record EqC {Σ} (τ : Type Σ ∗) : Set where
  field
    eqDict : ∀ {Γ : Cxt Σ} → Expr Σ Γ (con `Eq` $ τ)

open EqC {{...}} public

`eq` : ∀ {Σ} {Γ : Cxt Σ} {τ : Type Σ ∗} {{dict : EqC {Σ} τ}} →
         Expr Σ Γ τ → Expr Σ Γ τ → Expr Σ Γ (con `Bool`)
`eq` {τ = τ} e₁ e₂ = `==` [ τ ] $ eqDict $ e₁ $ e₂

instance
  `EqBool` : ∀ {Σ} → EqC {Σ} (con `Bool`)
  `EqBool` = record { eqDict = fdict fdict }

  `EqChar` : ∀ {Σ} → EqC {Σ} (con `Char`)
  `EqChar` = record { eqDict = fdict fdict }



typesInConstructors : (adt : ADT ∗) → Cxt []
typesInConstructors adt
  = map (transplant []) (concatMap dataConArgs (adtDataCons adt))

RequiredEq : ADT ∗ → Set
RequiredEq adt = All EqC (typesInConstructors adt)

firstBinder : ∀ {A : Set} {x y : A} {xs ys zs : List A} →
                x ∈ (xs +++ (x ∷ (ys ++ (xs +++ (y ∷ (ys ++ zs))))))
firstBinder {xs = xs} = ∈-+++-suffix {ys = xs} hd

secondBinder : ∀ {A : Set} {x y : A} {xs ys zs : List A} →
                 x ∈ (xs +++ (y ∷ (ys ++ (xs +++ (x ∷ (ys ++ zs))))))
secondBinder {_} {x} {_} {xs} {ys} {zs}
  = ∈-+++-suffix {ys = xs}
    (tl (∈-++-suffix {ys = ys} (∈-+++-suffix {ys = xs} hd)))



findDict : ∀ {adt : ADT ∗} {{eqs : RequiredEq adt}} {Γ : Cxt []} →
             (τ : Type [] ∗) →
             τ ∈ typesInConstructors adt →
             Expr [] Γ (con `Eq` $ τ)
findDict {_} {{eqs}} {_} τ p = EqC.eqDict (∈-All eqs p)


compareArgs : ∀ {adt : ADT ∗} → {{eqs : RequiredEq adt}}
                (binders : Cxt []) →
                (p : binders ⊆ typesInConstructors adt) →
                (τs : List (Type [] ∗)) →
                Expr [] (binders +++ (τs ++ binders +++
                         (τs ++ con (adtTyCon adt) ∷ con (adtTyCon adt) ∷ [])))
                        (con `Bool`)
compareArgs [] _ _ = con `True`
compareArgs {adt} (τ ∷ binders) p τs
  = `&&` $ (`==` [ τ ] $
            findDict {adt = adt} τ (∈-over-⊆ p hd) $
            var (firstBinder {xs = binders} {ys = τs}) $
            var (secondBinder {xs = binders} {ys = τs}))
         $ compareArgs binders (⊆-trans (⊆-skip id) p) (τ ∷ τs)

⊆-p : ∀ (adt : ADT ∗) (dc : DataCon (adtTyCon adt)) →
        patBinders {tyArgs = []} (con dc) ⊆ typesInConstructors adt
⊆-p adt (con ._ i)
  = ⊆-map-inj (λ p → ∈-concatMap p (∈-map-inj (Fin∈allFin i)))


makeNestedBranch : ∀ {adt : ADT ∗} {{eqs : RequiredEq adt}} →
                     (dc dc′ : DataCon (adtTyCon adt)) →
                     Branch [] (patBinders (con dc) +++
                                con (adtTyCon adt) ∷ con (adtTyCon adt) ∷ [])
                               adt [] (con `Bool`)
makeNestedBranch {adt} dc dc′ with dc == dc′
... | no ¬eq = alt (con dc′) (con `False`)
... | yes eq = alt (con dc) (compareArgs (patBinders (con dc))
                                         (⊆-p adt dc) [])


makeNestedBranchExhaustive : ∀ {adt : ADT ∗} {{eqs : RequiredEq adt}} →
  (dc : DataCon (adtTyCon adt)) →
  Exhaustive (map (makeNestedBranch dc) (adtDataCons adt))
makeNestedBranchExhaustive {adt} {{eqs}} dc rewrite
  compose-map (allFin (ADT.nbConstructors adt))
              (con adt) (makeNestedBranch dc) |
  compose-map (allFin (ADT.nbConstructors adt))
              (makeNestedBranch dc ∘ con adt)
              branchConstructorIndex
  = rewrite-∘-in-map dc _
  where
    bci-NestedBranch : ∀ {adt : ADT ∗} {dc dc′ : DataCon (adtTyCon adt)}
                         {{eqs : RequiredEq adt}} →
                         branchConstructorIndex (makeNestedBranch dc dc′)
                         ≡ just (dataConIndex dc′)
    bci-NestedBranch {adt} {dc} {dc′} {{eqs}} with dc == dc′
    ... | no ¬eq = refl
    ... | yes eq rewrite eq = refl

    rewrite-∘-in-map : ∀ {adt : ADT ∗} {{eqs : RequiredEq adt}} →
                         (dc : DataCon (adtTyCon adt)) →
                         (fins : List (Fin (ADT.nbConstructors adt))) →
                         map just fins ≡
                         map (branchConstructorIndex ∘ makeNestedBranch dc ∘ con adt)
                             fins
    rewrite-∘-in-map dc [] = refl
    rewrite-∘-in-map {adt} {{eqs}} dc (f ∷ fins) rewrite
      bci-NestedBranch {adt} {dc = dc} {dc′ = con adt f} {{eqs}} |
      rewrite-∘-in-map dc fins = refl

makeBranch : ∀ {adt : ADT ∗} {{eqs : RequiredEq adt}} →
               (dc : DataCon (adtTyCon adt)) →
               Branch [] (con (adtTyCon adt) ∷ con (adtTyCon adt) ∷ [])
                         adt [] (con `Bool`)
makeBranch {adt} dc
  = alt (con dc) (match adt []
                        (var (∈-+++-suffix {ys = patBinders (con dc)} hd))
                        (map (makeNestedBranch dc) (adtDataCons adt))
                        (makeNestedBranchExhaustive dc))

makeBranchExhaustive : ∀ {adt : ADT ∗} {{eqs : RequiredEq adt}} →
                         Exhaustive (map makeBranch (adtDataCons adt))
makeBranchExhaustive {adt} {{eqs}} rewrite
  compose-map (allFin (ADT.nbConstructors adt))
              (con adt) makeBranch |
  compose-map (allFin (ADT.nbConstructors adt))
              (makeBranch ∘ con adt) branchConstructorIndex
  = refl


deriveEq : (adt : ADT ∗) (eqs : RequiredEq adt) →
           Expr [] [] (con (adtTyCon adt) ⇒ con (adtTyCon adt) ⇒ con `Bool`)
deriveEq adt eqs
  = lam (con (con adt)) (lam (con (adtTyCon adt))
                             (match adt [] (var (tl hd))
                                    (map makeBranch (adtDataCons adt))
                                    makeBranchExhaustive))

-- data Foo = Barry | Bar Bool


-- `eqFoo` : Expr [] [] (con `Foo` ⇒ con `Foo` ⇒  con `Bool`)
-- `eqFoo` = lam (con `Foo`) (lam (con `Foo`)
--               (match FooADT [] (var (tl hd))
--                      (alt (con `Barry`)
--                           (match FooADT [] (var hd)
--                           (alt (con `Barry`) (con `True`) ∷
--                             alt (con `Bar`) (con `False`) ∷ []) refl) ∷
--                       alt (con `Bar`)
--                           (match FooADT [] (var (tl hd))
--                           (alt (con `Barry`) (con `False`) ∷
--                           alt (con `Bar`) (`eq` (var (tl hd)) (var hd)) ∷ [])
--                           refl)
--                       ∷ []) refl))

`eqFoo` : Expr [] [] (con `Foo` ⇒ con `Foo` ⇒  con `Bool`)
`eqFoo` = deriveEq FooADT (`EqBool` ∷ [])
