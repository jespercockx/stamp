module DeriveLenses where

open import MyPrelude hiding (_$_; [_]; show)
open import TypedCore
open import HelloWorld using (`Char`)

-- TODO move these to a better location
open import DeriveEq using (mkΛ; mkLam; mkFun)

-- postulate
--   weakenExpr : ∀ {Σ₁ Σ₂ Γ} {τ₁ : Type Σ₁ ∗} → Expr Σ₁ Γ τ₁ → (p : Σ₁ ⊆ Σ₂) →
--                  Expr Σ₂ (weakenCxt Γ p) (weakenType τ₁ p)

`Functor` : TyCon ((∗ ⇒ ∗) ⇒ ∗)
`Functor` = con (makeADT (fcon "GHC.Base" "Functor") [])

-- fmap :: forall f a b. Functor f => (a -> b) -> f a -> f b
`fmap` : ∀ {Σ} {Γ : Cxt Σ} →
           Expr Σ Γ (forAll (∗ ⇒ ∗)
                    (forAll ∗
                    (forAll ∗
                    ((con `Functor` $ tvar (tl (tl hd))) ⇒
                     (tvar (tl hd) ⇒ tvar hd) ⇒
                     (tvar (tl (tl hd)) $ tvar (tl hd)) ⇒
                     (tvar (tl (tl hd)) $ tvar hd)))))
`fmap` = fvar (fvar "GHC.Base" "fmap")


-- Lens' a b = forall (f :: * -> *). Functor f => (b -> f b) -> a -> f a
`Lens` : ∀ {Σ} → (a b : Type Σ ∗) → Type Σ ∗
`Lens` a b = forAll (∗ ⇒ ∗)
                    ((con `Functor` $ tvar hd) ⇒
                     (weakenType b (⊆-skip ⊆-refl) ⇒
                      tvar hd $ weakenType b (⊆-skip ⊆-refl)) ⇒
                     weakenType a (⊆-skip ⊆-refl) ⇒
                     tvar hd $ weakenType a (⊆-skip ⊆-refl))


-- data ARecord a
--   = ARecord
--     { _aBool :: Bool
--     , _aChar :: Char
--     , _anA   :: a
--     }


ARecordADT : ADT (∗ ⇒ ∗)
ARecordADT = makeADT (fcon "Data" "ARecord")
                     ((fcon "Data" "ARecord" ,
                       con `Bool` ∷ con `Char` ∷ tvar hd ∷ [])
                       ∷ [])

`ARecord` : TyCon (∗ ⇒ ∗)
`ARecord` = con ARecordADT

`aRecord` : DataCon `ARecord`
`aRecord` = con ARecordADT zero



-- aBool f a
--   = ((\ x_a2vu -> a {_aBool = x_a2vu}) `fmap` (f (_aBool a)))

-- aBool
--   :: forall (f_a2Cp :: * -> *) a_a2Cq.
--      Functor f_a2Cp =>
--      (Bool -> f_a2Cp Bool) -> ARecord a_a2Cq -> f_a2Cp (ARecord a_a2Cq)
-- aBool =
--   \ (@ (f_a2Ct :: * -> *))
--     (@ a_a2Cu)
--     ($dFunctor_a2Cv :: Functor f_a2Ct)
--     (f1_a2vx :: Bool -> f_a2Ct Bool)
--     (a1_a2vy :: ARecord a_a2Cu) ->
--     fmap
--       @ f_a2Ct
--       $dFunctor_a2Cv
--       @ Bool
--       @ (ARecord a_a2Cu)
--       (\ (x_a2vu :: Bool) ->
--          case a1_a2vy of _ { ARecord ds_d2CZ ds1_d2D0 ds2_d2D1 ->
--          ARecord @ a_a2Cu x_a2vu ds1_d2D0 ds2_d2D1
--          })
--       (f1_a2vx
--          (case a1_a2vy of _ { ARecord ds_d2D4 ds1_d2D5 ds2_d2D6 ->
--           ds_d2D4
--           }))

`aBool` : Expr [] [] (mkForAll (ADT.tyCxt ARecordADT)
                               (`Lens` (tyConType `ARecord`) (con `Bool`)))
`aBool` = Λ ∗
         (Λ (∗ ⇒ ∗)
         (lam (con `Functor` $ tvar hd)
         (lam (con `Bool` ⇒ tvar hd $ con `Bool`)
         (lam (con `ARecord` $ tvar (tl hd))
         (`fmap` [ tvar hd  ]  [ con `Bool` ] [ con `ARecord` $ tvar (tl hd) ] $
          var (tl (tl hd)) $
          lam (con `Bool`)
              (match ARecordADT (tvar (tl hd) ∷ []) (var (tl hd))
                     (alt (con `aRecord`)
                          (con `aRecord` [ tvar (tl hd) ] $
                           var (tl (tl (tl hd))) $
                           var (tl hd) $
                           var hd) ∷ [])
                     refl) $
          (var (tl hd) $
           match ARecordADT (tvar (tl hd) ∷ []) (var hd)
                (alt (con `aRecord`)
                     (var (tl (tl hd))) ∷ [])
                refl))))))


SingleConstructor : ∀ {κ} → ADT κ → Set
SingleConstructor adt = ADT.nbConstructors adt ≡ 1

singleConstructor : ∀ {κ} → (adt : ADT κ) → SingleConstructor adt →
                      ForeignDataCon × Cxt (ADT.tyCxt adt)
singleConstructor (Adt _ .1 (c ∷ [])) refl = c

singleDataCon : ∀ {κ} → (adt : ADT κ) → SingleConstructor adt →
                  DataCon (adtTyCon adt)
singleDataCon (Adt ftc .1 (c ∷ [])) refl = con (Adt ftc 1 (c ∷ [])) zero



singleDataConADT : ∀ {κ} → (adt : ADT κ) → (single : SingleConstructor adt) →
                     dataConADT (singleDataCon adt single) ≡ adt
singleDataConADT (Adt _ .1 (c ∷ [])) refl = refl

singleDataConExhaustive :
  ∀ {κ} → (adt : ADT κ) → (single : SingleConstructor adt) →
    {Γ : Cxt (ADT.tyCxt adt)} {τ : Type (ADT.tyCxt adt) ∗}
    (tyArgs : Types (ADT.tyCxt adt) (ADT.tyCxt adt)) →
    {e : Expr (ADT.tyCxt adt)
              (patBinders {tyArgs = tyArgs}
                          (con (singleDataCon adt single)) +++ Γ) τ} →
    Exhaustive (alt (con (singleDataCon adt single)) e ∷ [])
singleDataConExhaustive (Adt _ .1 (c ∷ [])) refl tyArgs = refl



∈-≡ : ∀ {A : Set} {x y : A} {xs : List A} → x ∈ (x ∷ xs) → x ≡ y → y ∈ (x ∷ xs)
∈-≡ p refl = p


-- dcType2 : ∀ {κ} {tc : TyCon κ} → DataCon tc → Type (satTyCxt (saturate κ)) ∗
-- dcType2 {κ} dc = mkFunRev (dataConArgs dc) (tyConType (con adt))
--   where
--     adt : ADT κ
--     adt = dataConADT dc




-- [_]ADT : ∀ {κ} {adt : ADT κ} {Σ} {Γ : Cxt Σ}
--            {τ : Type (ADT.tyCxt adt +++ Σ) ∗} →
--            Expr Σ Γ (mkForAll+++ (ADT.tyCxt adt) τ) →
--            Expr (satTyCxt (saturate κ)) (weakenCxt Γ ?) τ
-- [_]ADT e = {!!}




-- applyTyArgsExpr : ∀ {κ} {adt : ADT κ} {Γ : Cxt (ADT.tyCxt adt)} →
--                     Expr (ADT.tyCxt adt) Γ (con (adtTyCon adt)) →
--                     Expr (ADT.tyCxt adt) Γ
--                          (applyTyArgs (con (adtTyCon adt))
--                                       (Types-Σ (ADT.tyCxt adt)))
-- applyTyArgsExpr e = ?

-- After pattern matching on a record, reassemble the record whereby one field
-- is replaced by another.
--
-- E.g. in the following expression:
--
--     case a of _ { ARecord x y z ->
--       ARecord @ a x repl z }
--
-- The RHS of the single branch is what we will return.
--
-- reassembleRecord : ∀ {κ} (adt : ADT κ) →
--                      (single : SingleConstructor adt) →



-- Goal: Expr ((∗ ⇒ ∗) ∷ ADT.tyCxt adt)
--       (map
--        (substTyArgs (weakenTypes (Types-Σ (ADT.tyCxt adt)) (λ {.x} → tl)))
--        (dataConArgs (singleDataCon adt single))
--        +++
--        substTop (weakenType (tyConType (adtTyCon adt)) (λ {.x} → tl))
--        (weakenType (weakenType fld (λ {.x} → tl))
--         (λ {.x} → ⊆-skip (λ {.x₁} → ⊆-refl)))
--        ∷
--        weakenType (tyConType (adtTyCon adt)) (λ {.x} → tl) ∷
--        (weakenType fld (λ {.x} → tl) ⇒
--         tvar hd $ weakenType fld (λ {.x} → tl))
--        ∷ (con `Functor` $ tvar hd) ∷ [])
--       (weakenType (tyConType (adtTyCon adt)) (λ {.x} → tl))
-- ————————————————————————————————————————————————————————————
-- single : SingleConstructor adt
-- p      : fld ∈ flds
-- fld    : Type (ADT.tyCxt adt) ∗
-- flds   : Cxt (ADT.tyCxt adt)
-- adt    : ADT .κ
-- .κ     : Kind


-- (weakenExpr
--                         (applyDCFunArgs (singleDataCon adt single)
--                         (applyDCTyArgs (singleDataCon adt single)
--                         (transport _ (singleDataConADT adt single)
--                         (con (singleDataCon adt single)) ))) tl)

--   \ (@ (f_a2Ct :: * -> *))
--     (@ a_a2Cu)
--     ($dFunctor_a2Cv :: Functor f_a2Ct)
--     (f1_a2vx :: Bool -> f_a2Ct Bool)
--     (a1_a2vy :: ARecord a_a2Cu) ->

-- forAll (∗ ⇒ ∗)
--                     ((con `Functor` $ tvar hd) ⇒
--                      (weakenType b tl ⇒ tvar hd $ weakenType b tl) ⇒
--                       weakenType a tl ⇒ tvar hd $ weakenType a tl)




∈-skip-adt : ∀ {κ κ′} → (adt : ADT κ′) → κ ∈ (ADT.tyCxt adt ++ κ ∷ [])
∈-skip-adt adt = ∈-++-suffix {ys = ADT.tyCxt adt} hd


mkForAll++ : ∀ (Σ₁ : TyCxt) {Σ₂ : TyCxt} → Type (Σ₁ ++ Σ₂) ∗ → Type Σ₂ ∗
mkForAll++ []       τ = τ
mkForAll++ (κ ∷ Σ₁) τ = mkForAll++ Σ₁ (forAll κ τ)



mkΛ++ : ∀ (Σ₁ : TyCxt) {Σ₂ : TyCxt} {τ : Type (Σ₁ ++ Σ₂) ∗} →
          Expr (Σ₁ ++ Σ₂) [] τ → Expr Σ₂ [] (mkForAll++ Σ₁ τ)
mkΛ++ []      e = e
mkΛ++ (κ ∷ Σ) e = mkΛ++ Σ (Λ κ e)



Types-Σ′ : ∀ Σ Σ′ → (p : Σ ⊆ Σ′) → Types Σ′ Σ
Types-Σ′ []      _  _         = []
Types-Σ′ (κ ∷ Σ) Σ′ (p₁ , p₂) = tvar p₁ ∷ weakenTypes (Types-Σ′ Σ Σ′ p₂) ⊆-refl


-- case a of _ { ARecord x y z -> x }
getField : ∀ {κ} {adt : ADT κ} {Γ : Cxt (ADT.tyCxt adt)} →
             (single : SingleConstructor adt) →
             (fld : Type (ADT.tyCxt adt) ∗) →
             fld ∈ patBinders {tyArgs = Types-Σ (ADT.tyCxt adt)}
                              (con (singleDataCon adt single))  →
             Expr (ADT.tyCxt adt) Γ (tyConType (adtTyCon adt)) →
             Expr (ADT.tyCxt adt) Γ fld
getField {κ} {Adt ftc .1 (c ∷ [])} refl fld fld∈ e
  = match (Adt {κ = κ} ftc 1 (c ∷ [])) (Types-Σ _) e
          (alt (con (con (Adt ftc 1 (c ∷ [])) zero))
               (var (∈-+++-prefix fld∈)) ∷ [])
          refl

applyDCTyArgs : ∀ {κ} {adt : ADT κ} {Γ : Cxt (ADT.tyCxt adt)} →
                  (dc : DataCon (adtTyCon adt)) →
                  Expr (ADT.tyCxt adt) Γ
                       (weakenType
                        (mkForAll (ADT.tyCxt adt)
                                  (mkFunRev (dataConArgs dc)
                                            (tyConType (con adt))))
                                            tt) →
                  Expr (ADT.tyCxt adt) Γ
                       (mkFunRev (dataConArgs dc)
                                 (tyConType (con adt)))
applyDCTyArgs = {!!}



applyDCFunArgs : ∀ {κ} {adt : ADT κ} {Γ : Cxt (ADT.tyCxt adt)} →
                  (dc : DataCon (adtTyCon adt)) →
                  Expr (ADT.tyCxt adt) Γ
                       (mkFunRev (dataConArgs dc)
                                 (tyConType (con adt))) →
                  Expr (ADT.tyCxt adt) Γ (tyConType (con adt))
applyDCFunArgs = {!!}



-- case a of _ { ARecord x y z -> ARecord @ a x repl z }
setField : ∀ {κ} {adt : ADT κ} {Γ : Cxt (ADT.tyCxt adt)} →
             (single : SingleConstructor adt) →
             (fld : Type (ADT.tyCxt adt) ∗) →
             fld ∈ patBinders {tyArgs = Types-Σ (ADT.tyCxt adt)}
                              (con (singleDataCon adt single)) →
             Expr (ADT.tyCxt adt) Γ (tyConType (adtTyCon adt)) →
             Expr (ADT.tyCxt adt) Γ (tyConType (adtTyCon adt))
setField {κ} {Adt ftc .1 (c ∷ [])} refl fld fld∈ e
  = let adt : ADT κ
        adt = Adt ftc 1 (c ∷ [])
    in match adt (Types-Σ _) e
             (alt (con (con adt zero))
                  (applyDCFunArgs (con adt zero)
                  (applyDCTyArgs (con adt zero) {!e!}))  ∷ [])
             refl
-- (applyDCFunArgs {!con adt zero!} (applyDCTyArgs {!!} {!!}))



makeLensForField :
  ∀ {κ} {adt : ADT κ} → (flds : Cxt (ADT.tyCxt adt)) →
    (fld : Type (ADT.tyCxt adt) ∗) → fld ∈ flds →
    SingleConstructor adt →
    Expr [] []
         (forAll (∗ ⇒ ∗)
         (mkForAll++ (ADT.tyCxt adt)
         ((con `Functor` $ tvar (∈-skip-adt adt)) ⇒
         weakenType fld {!!} ⇒ {!!})))
makeLensForField {κ} {adt} flds fld p single
  = Λ (∗ ⇒ ∗) {!!}



-- makeLensForField :
--   ∀ {κ} {adt : ADT κ} → (flds : Cxt (ADT.tyCxt adt)) →
--     (fld : Type (ADT.tyCxt adt) ∗) → fld ∈ flds →
--     SingleConstructor adt →
--     Expr [] []
--          (forAll (∗ ⇒ ∗)
--          (mkForAll++ (ADT.tyCxt adt)
--          ((con `Functor` $ tvar (∈-skip-adt adt)) ⇒
--           (weakenType fld ∈-++-prefix ⇒
--            tvar (∈-skip-adt adt) $ weakenType fld ∈-++-prefix) ⇒
--           weakenType (tyConType (adtTyCon adt)) ∈-++-prefix  ⇒
--           tvar (∈-skip-adt adt) $ weakenType (tyConType (adtTyCon adt)) ∈-++-prefix)))
-- makeLensForField {κ} {adt} flds fld p single
--   = Λ (∗ ⇒ ∗)
--       (mkΛ++ (ADT.tyCxt adt)
--       (lam (con `Functor` $ tvar (∈-skip-adt adt))
--       (lam (weakenType fld ∈-++-prefix ⇒
--             tvar (∈-skip-adt adt) $ weakenType fld ∈-++-prefix)
--       (lam (weakenType (tyConType (adtTyCon adt)) ∈-++-prefix)
--       ((`fmap` [ tvar (∈-skip-adt adt) ] [ weakenType fld ∈-++-prefix ]
--                [ weakenType (tyConType (adtTyCon adt)) ∈-++-prefix ] $
--         var (tl (tl hd)) $
--         lam (substTop (weakenType (tyConType (adtTyCon adt)) ∈-++-prefix)
--                       (weakenType (weakenType fld ∈-++-prefix) (⊆-skip ⊆-refl)))
--             (match adt (Types-Σ′ (ADT.tyCxt adt) _ ∈-++-prefix)
--                    {!!} {!!} {!!}) $
--         (var {!!} $ {!!})))))))

{-

-- (singleDataConExhaustive adt single (Types-Σ (ADT.tyCxt adt))))))))))

-- singleDataConExhaustive :
--   ∀ {κ} → (adt : ADT κ) → (single : SingleConstructor adt) →
--     {Γ : Cxt (ADT.tyCxt adt)} {τ : Type (ADT.tyCxt adt) ∗}
--     (tyArgs : Types (ADT.tyCxt adt) (ADT.tyCxt adt)) →
--     {e : Expr (ADT.tyCxt adt)
--               (patBinders {tyArgs = tyArgs}
--                           (con (singleDataCon adt single)) +++ Γ) τ} →
--     Exhaustive (alt (con (singleDataCon adt single)) e ∷ [])

--       (f1_a2vx
--          (case a1_a2vy of _ { ARecord ds_d2D4 ds1_d2D5 ds2_d2D6 ->
--           ds_d2D4
--           }))


-- makeLensForField : ∀ {κ} {adt : ADT κ} → (flds : Cxt (ADT.tyCxt adt)) →
--                      (fld : Type (ADT.tyCxt adt) ∗) → fld ∈ flds →
--                      SingleConstructor adt →
--                      Expr [] [] (mkForAll (ADT.tyCxt adt)
--                                           (`Lens` (tyConType (adtTyCon adt))
--                                                   fld))
-- makeLensForField {_} {adt} flds fld p single
--   = mkΛ (ADT.tyCxt adt)
--         (Λ (∗ ⇒ ∗)
--         (lam (con `Functor` $ tvar hd)
--         (lam (weakenType fld tl ⇒ tvar hd $ weakenType fld tl)
--         (lam (weakenType (tyConType (adtTyCon adt)) tl)
--         (`fmap` [ tvar hd ] [ weakenType fld tl ]
--                 [ weakenType (tyConType (adtTyCon adt)) tl ] $
--         var (tl (tl hd)) $
--         lam (substTop (weakenType (tyConType (adtTyCon adt)) tl)
--                       (weakenType (weakenType fld tl) (⊆-skip ⊆-refl)))
--             (match adt (weakenTypes (Types-Σ (ADT.tyCxt adt)) tl)
--                    (var (tl (∈-≡ hd (sym (weakenType-applyTyArgs adt)))))
--                    (alt (con (singleDataCon adt single))
--                         {!!} ∷ [])
--                         {!!}) $
--         (var (tl {!hd!}) $
--          match adt (weakenTypes (Types-Σ (ADT.tyCxt adt)) tl)
--                (var (∈-≡ hd (sym (weakenType-applyTyArgs adt))))
--                ({!!} ∷ [])
--                {!!}))))))



deriveLenses : ∀ {κ} → (adt : ADT κ) → (single : SingleConstructor adt) →
               All (λ τ → Expr [] [] (mkForAll (ADT.tyCxt adt)
                                      (`Lens` (tyConType (adtTyCon adt)) τ)))
                   (snd (singleConstructor adt single))
deriveLenses adt single = {!!}
-}
