module DeriveEq where

open import MyPrelude hiding (_$_; [_]; show)
open import TypedCore
open import TypedUtils
open import HelloWorld

FooADT : ADT ∗
FooADT = makeADT (fcon "Data" "Foo")
                 ((fcon "Data" "Barry" , []) ∷ (fcon "Data" "Bar" , con `Bool` ∷ []) ∷ [])

`Foo` : TyCon ∗
`Foo` = con FooADT

`Barry` : DataCon `Foo`
`Barry` = con FooADT zero

`Bar` : DataCon `Foo`
`Bar` = con FooADT (suc zero)


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


typesInConstructors : ∀ {κ} → (adt : ADT κ) → Cxt (ADT.tyCxt adt)
typesInConstructors adt
  = map (applyTySubst IdS)
        (concatMap dataConArgs (adtDataCons adt))

-- Type doesn't contain a type variable or forAll
closedType : ∀ {κ Σ} → Type Σ κ → Bool
closedType (tvar x) = false
closedType (τ₁ $ τ₂) = closedType τ₁ || closedType τ₂
closedType (τ₁ ⇒ τ₂) = closedType τ₁ || closedType τ₂
closedType (forAll _ _) = false
closedType (con _) = true
closedType (lit _) = true

openType : ∀ {κ Σ} → Type Σ κ → Bool
openType = not ∘ closedType

RequiredEqAtCompileTime : ∀ {κ} → ADT κ → Set
RequiredEqAtCompileTime adt
  = All EqC (filter closedType (typesInConstructors adt))


RequiredEqAtRunTime : ∀ {κ} → (adt : ADT κ) → Cxt (ADT.tyCxt adt)
RequiredEqAtRunTime adt
  = reverse (map (_$_ (con `Eq`)) (filter openType (typesInConstructors adt)))



firstBinder : ∀ {A : Set} {x y : A} {xs ys zs : List A} →
                x ∈ (xs +++ (x ∷ (ys ++ (xs +++ (y ∷ (ys ++ zs))))))
firstBinder {xs = xs} = ∈-+++-suffix {ys = xs} hd

secondBinder : ∀ {A : Set} {x y : A} {xs ys zs : List A} →
                 x ∈ (xs +++ (y ∷ (ys ++ (xs +++ (x ∷ (ys ++ zs))))))
secondBinder {_} {x} {_} {xs} {ys} {zs}
  = ∈-+++-suffix {ys = xs}
    (tl (∈-++-suffix {ys = ys} (∈-+++-suffix {ys = xs} hd)))


findDict : ∀ {κ} {adt : ADT κ} {{eqs : RequiredEqAtCompileTime adt}} →
             {binders τs : Cxt (ADT.tyCxt adt)} →
             (τ : Type (ADT.tyCxt adt) ∗) →
             τ ∈ typesInConstructors adt →
             Expr (ADT.tyCxt adt)
                  (binders +++ τ ∷ τs ++ binders +++ τ ∷ τs ++
                   tyConType (adtTyCon adt) ∷ tyConType (adtTyCon adt) ∷
                   RequiredEqAtRunTime adt)
                  (con `Eq` $ τ)
findDict {_} {adt} {{eqs}} {binders} {τs} τ p with closedType τ == true
... | yes closed = EqC.eqDict (∈-All eqs (∈-filter p closed))
... | no ¬closed = var (∈-+++-suffix {ys = binders}
                       (tl
                       (∈-++-suffix {ys = τs}
                       (∈-+++-suffix {ys = binders}
                       (tl
                       (∈-++-suffix {ys = τs}
                       (tl
                       (tl
                       (∈-reverse
                       (∈-map-inj (∈-filter-not p ¬closed)))))))))))


compareArgs : ∀ {κ} {adt : ADT κ} → {{eqs : RequiredEqAtCompileTime adt}}
                (binders τs : Cxt (ADT.tyCxt adt)) →
                (p : binders ⊆ typesInConstructors adt) →
                Expr (ADT.tyCxt adt)
                     (binders +++ (τs ++ binders +++
                      (τs ++ tyConType (adtTyCon adt) ∷
                             tyConType (adtTyCon adt) ∷
                       RequiredEqAtRunTime adt)))
                     (con `Bool`)
compareArgs [] _ _ = con `True`
compareArgs {κ} {adt} (τ ∷ binders) τs p
  = `&&` $ (`==` [ τ ] $
           findDict {κ} {adt} {binders} {τs} τ (∈-over-⊆ p hd) $
            var (firstBinder {xs = binders} {ys = τs}) $
            var (secondBinder {xs = binders} {ys = τs}))
         $ compareArgs {adt = adt} binders (τ ∷ τs)
                       (⊆-trans (⊆-skip ⊆-refl) p)


⊆-p : ∀ {κ} → (adt : ADT κ) → (dc : DataCon (adtTyCon adt)) →
        patBinders {tyArgs = IdS} (con dc)
        ⊆ typesInConstructors adt
⊆-p adt (con ._ i)
  = ⊆-map-inj (⊆-over-∈ (λ p → ∈-concatMap p (∈-map-inj (Fin∈allFin i))))

makeNestedBranchRHS : ∀ {κ} {adt : ADT κ} {{eqs : RequiredEqAtCompileTime adt}} →
                     (dc dc′ : DataCon (adtTyCon adt)) →
                     Expr (ADT.tyCxt adt)
                          (patBinders (con dc′) +++ patBinders (con dc) +++
                          tyConType (adtTyCon adt) ∷ tyConType (adtTyCon adt) ∷
                          RequiredEqAtRunTime adt) (con `Bool`)
makeNestedBranchRHS {adt = adt} dc dc′ with dc == dc′
makeNestedBranchRHS {adt = adt} dc dc′ | no ¬eq = con `False`
makeNestedBranchRHS {adt = adt} dc .dc | yes refl =
  compareArgs {adt = adt} (patBinders (con dc)) [] (⊆-p adt dc)

makeNestedBranch : ∀ {κ} {adt : ADT κ} {{eqs : RequiredEqAtCompileTime adt}} →
                     (dc dc′ : DataCon (adtTyCon adt)) →
                     Branch (ADT.tyCxt adt)
                            (patBinders {tyArgs = IdS}
                                        (con dc) +++
                            tyConType (adtTyCon adt) ∷
                            tyConType (adtTyCon adt) ∷
                            RequiredEqAtRunTime adt)
                            adt IdS (con `Bool`)
makeNestedBranch dc dc′ = alt (con dc′) (makeNestedBranchRHS dc dc′)

makeNestedBranchExhaustive :
  ∀ {κ} {adt : ADT κ} {{eqs : RequiredEqAtCompileTime adt}} →
    (dc : DataCon (adtTyCon adt)) →
    Exhaustive (λ i → makeNestedBranch dc (con adt i))
makeNestedBranchExhaustive {_} {adt} {{eqs}} dc i = refl

makeBranch : ∀ {κ} {adt : ADT κ} {{eqs : RequiredEqAtCompileTime adt}} →
               (dc : DataCon (adtTyCon adt)) →
               Branch (ADT.tyCxt adt) (tyConType (adtTyCon adt) ∷
                                       tyConType (adtTyCon adt) ∷
                                       RequiredEqAtRunTime adt)
                      adt IdS (con `Bool`)
makeBranch {_} {adt} dc
  = alt (con dc)
        (match adt IdS
               (var (∈-+++-suffix {ys = patBinders (con dc)} hd))
               (λ i → makeNestedBranch dc (con adt i))
               (makeNestedBranchExhaustive dc))

makeBranchExhaustive : ∀ {κ} {adt : ADT κ}
                         {{eqs : RequiredEqAtCompileTime adt}} →
                         Exhaustive (λ i → makeBranch (con adt i))
makeBranchExhaustive {_} {adt} {{eqs}} i = refl


deriveEqType : ∀ {κ} → ADT κ → Type [] ∗
deriveEqType adt = mkForAll (ADT.tyCxt adt)
                            (RequiredEqAtRunTime adt ⇒ⁿ
                            (tyConType (adtTyCon adt) ⇒
                              tyConType (adtTyCon adt) ⇒
                              con `Bool`))

deriveEq : ∀ {κ} → (adt : ADT κ) (eqs : RequiredEqAtCompileTime adt) →
           Expr [] [] (deriveEqType adt)
deriveEq adt eqs
  = mkΛ (ADT.tyCxt adt)
    (lamⁿ {Γ = RequiredEqAtRunTime adt} 
    (lam (tyConType (adtTyCon adt)) 
    (lam (tyConType (adtTyCon adt)) 
    (match adt IdS (var (tl hd)) 
      (λ i → makeBranch (con adt i)) 
      (λ i → refl))))) 

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

`eqFoo` : Expr [] [] (deriveEqType FooADT)
`eqFoo` = deriveEq FooADT (`EqBool` ∷ [])


-- data Pair a b = Pair a b

PairADT : ADT (∗ ⇒ ∗ ⇒ ∗)
PairADT = makeADT (fcon "Data" "Pair")
                  ((fcon "Data" "Pair" , tvar (tl hd) ∷ tvar hd ∷ []) ∷ [])

`Pair` : TyCon (∗ ⇒ ∗ ⇒ ∗)
`Pair` = con PairADT

`pair` : DataCon `Pair`
`pair` = con PairADT zero


`eqPair` : Expr [] [] (deriveEqType PairADT)
`eqPair` = deriveEq PairADT []

-- `eqPair`
--   = Λ ∗
--    (Λ ∗
--    (lam (con `Eq` $ tvar (tl hd))
--    (lam (con `Eq` $ tvar hd)
--    (lam (con `Pair` $ tvar (tl hd) $ tvar hd)
--    (lam (con `Pair` $ tvar (tl hd) $ tvar hd)
--    (match PairADT (tvar hd ∷ tvar (tl hd) ∷ []) (var (tl hd))
--           (alt (con `pair`)
--                (match PairADT (tvar hd ∷ tvar (tl hd) ∷ []) (var (tl (tl hd)))
--                       (alt (con `pair`)
--                            (`&&`
--                            $ (`==` [ tvar (tl hd) ]
--                              $ var (tl (tl (tl (tl (tl (tl (tl hd)))))))
--                              $ var (tl hd) $ var (tl (tl (tl hd))))
--                            $ (`==` [ tvar hd ]
--                              $ var (tl (tl (tl (tl (tl (tl hd))))))
--                              $ var hd $ var (tl (tl hd)))) ∷ [])
--                             refl)
--                            ∷ []) refl))))))
