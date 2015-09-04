module TypedCore where

{-# IMPORT TysWiredIn #-}

open import MyPrelude hiding (_$_; [_])
open import CoreSyn
  hiding (module Type; module Expr; Expr; TyCon; DataCon)
  renaming (Kind to CKind; Type to CType)
open import Tactic.Deriving.Eq

data Kind : Set where
  ∗   : Kind
  _⇒_ : Kind → Kind → Kind

⇒-inj₁ : ∀ {κ₁₁ κ₁₂ κ₂₁ κ₂₂} → (κ₁₁ ⇒ κ₁₂) ≡ (κ₂₁ ⇒ κ₂₂) → κ₁₁ ≡ κ₂₁
⇒-inj₁ refl = refl

⇒-inj₂ : ∀ {κ₁₁ κ₁₂ κ₂₁ κ₂₂} → (κ₁₁ ⇒ κ₁₂) ≡ (κ₂₁ ⇒ κ₂₂) → κ₁₂ ≡ κ₂₂
⇒-inj₂ refl = refl

Context : Set → Set
Context = List

TyCxt : Set
TyCxt = Context Kind

Module : Set
Module = String

Ident : Set
Ident = String

data TyCon (κ : Kind) : Set

infixr 2 _⇒_

infixl 3 _$_

data Type (Σ : TyCxt) : Kind → Set where
  tvar   : ∀ {κ} → κ ∈ Σ → Type Σ κ
  _$_    : ∀ {κ₁ κ₂} → Type Σ (κ₁ ⇒ κ₂) → Type Σ κ₁ → Type Σ κ₂
  _⇒_    : Type Σ ∗ → Type Σ ∗ → Type Σ ∗
  forAll : ∀ κ → Type (κ ∷ Σ) ∗ → Type Σ ∗
  con    : ∀ {κ} → TyCon κ → Type Σ κ
  lit    : ∀ {κ} → TyLit → Type Σ κ -- TODO separate constructor?


private
  postulate
    todo  : ∀ {a} {A : Set a} → String → A

instance
  EqTyLit : Eq TyLit
  EqTyLit = todo "Eq TyLit"



typeTyCon : ∀ {Σ κ} → Type Σ κ → Maybe (∃ λ κ′ → TyCon κ′)
typeTyCon (con {κ} tc) = just (κ , tc)
typeTyCon (τ $ _)      = typeTyCon τ
typeTyCon _            = nothing

Cxt : TyCxt → Set
Cxt Σ = Context (Type Σ ∗)

--- Utilities for modelling Type Constructors
infixr 5 _∷_
data Saturates : Kind → Set where
  []  : Saturates ∗
  _∷_ : ∀ {κ} → (κ₁ : Kind) → Saturates κ → Saturates (κ₁ ⇒ κ)

saturate : ∀ κ → Saturates κ
saturate ∗ = []
saturate (κ₁ ⇒ κ₂) = κ₁ ∷ saturate κ₂

satTyCxt : ∀ {κ} → Saturates κ → TyCxt
satTyCxt [] = []
satTyCxt (κ ∷ sat) = satTyCxt sat ++ (κ ∷ [])

saturatedTyCxt : ∀ κ → TyCxt
saturatedTyCxt = satTyCxt ∘ saturate


satTyCxt-⊆ : ∀ {κ κₛ} → (sat : Saturates κₛ) → satTyCxt sat ⊆ satTyCxt (κ ∷ sat)
satTyCxt-⊆ sat = ⊆-over-∈ ∈-suffix

data ForeignTyCon : Set where
  fcon : Module → Ident → ForeignTyCon

data ForeignDataCon : Set where
  fcon : Module → Ident → ForeignDataCon

record ADT (κ : Kind) : Set where
  inductive
  constructor Adt

  tyCxt : TyCxt
  tyCxt = saturatedTyCxt κ

  field
    foreignTyCon : ForeignTyCon
    nbConstructors : Nat -- TODO make it a non-field?
    constructors : Vec (ForeignDataCon × Cxt tyCxt) nbConstructors

  constructorIndex : Set
  constructorIndex = Fin nbConstructors

open ADT {{...}} public

makeADT : ∀ {n} {κ} → ForeignTyCon →
            Vec (ForeignDataCon × Cxt (saturatedTyCxt κ)) n →
            ADT κ
makeADT {n} ftc cs = record { foreignTyCon = ftc
                            ; nbConstructors = n
                            ; constructors = cs
                            }

data TyCon κ where
  con : ∀ (adt : ADT κ) → TyCon κ

tyConADT : ∀ {κ} → TyCon κ → ADT κ
tyConADT (con adt) = adt

tyConCxt : ∀ {κ} → TyCon κ → TyCxt
tyConCxt = ADT.tyCxt ∘ tyConADT

-- TODO remove Foreign-?
tyConConstructors : ∀ {κ} → TyCon κ → List ForeignDataCon
tyConConstructors (con adt) = vecToList (fst <$> ADT.constructors adt)

adtTyCon : ∀ {κ} → ADT κ → TyCon κ
adtTyCon = con

typeADT : ∀ {Σ κ} → Type Σ κ → Maybe (∃ λ κ′ → ADT κ′)
typeADT (con {κ} (con adt)) = just (κ , adt)
typeADT (τ $ _)      = typeADT τ
typeADT _            = nothing


data DataCon {κ : Kind} : TyCon κ → Set where
  con : ∀ (adt : ADT κ) → (i : ADT.constructorIndex adt) → DataCon (con adt)


dataConADT : ∀ {κ} {tc : TyCon κ} → DataCon tc → ADT κ
dataConADT (con adt _) = adt

dataConForeignDataCon : ∀ {κ} {tc : TyCon κ} → DataCon tc → ForeignDataCon
dataConForeignDataCon (con adt i) = fst (indexVec (ADT.constructors adt) i)

dataConArgs : ∀ {κ} {tc : TyCon κ} → DataCon tc → Cxt (tyConCxt tc)
dataConArgs (con adt i) = snd (indexVec (ADT.constructors adt) i)

dataConIndex : ∀ {κ} {tc : TyCon κ} → DataCon tc →
                 ADT.constructorIndex (tyConADT tc)
dataConIndex (con _ i) = i

adtDataCons : ∀ {κ} → (adt : ADT κ) → List (DataCon (con adt))
adtDataCons adt = map (con adt) (allFin (ADT.nbConstructors adt))


mkForAll : ∀ (Σ : TyCxt) → Type Σ ∗ → Type [] ∗
mkForAll [] τ = τ
mkForAll (κ ∷ Σ) τ = mkForAll Σ (forAll κ τ)

mkFunRev : ∀ {Σ : TyCxt} → Cxt Σ → Type Σ ∗ → Type Σ ∗
mkFunRev []       τ = τ
mkFunRev (τ₁ ∷ Γ) τ = τ₁ ⇒ mkFunRev Γ τ

-- Problems to solve:
-- * Exhaustiveness: for `TyCon`, list all `DataCon`s
-- * Type check: given a `TyCon` and a `DataCon`, check that the type of the
-- latter includes the former
-- * Patterns: allow patterns to refer to `DataCon`s


--- Weakening and substitution


Types : TyCxt → List Kind → Set
Types Σ = All (Type Σ)

TySubst : TyCxt → TyCxt → Set
TySubst Σ₁ Σ₂ = Types Σ₂ Σ₁

WeakenS : ∀ {Σ₁ Σ₂} → Σ₁ ⊆ Σ₂ → TySubst Σ₁ Σ₂
WeakenS = mapAll tvar

IdS : ∀ {Σ} → TySubst Σ Σ
IdS = WeakenS ⊆-refl

weakenType : ∀ {Σ₁ Σ₂ κ} → Type Σ₁ κ → Σ₁ ⊆ Σ₂ → Type Σ₂ κ
weakenType (tvar i)     p = tvar (∈-over-⊆ p i)
weakenType (τ₁ $ τ₂)    p = weakenType τ₁ p $ weakenType τ₂ p
weakenType (τ₁ ⇒ τ₂)    p = weakenType τ₁ p ⇒ weakenType τ₂ p
weakenType (forAll κ τ) p = forAll κ (weakenType τ (⊆-keep p))
weakenType (con c)      p = con c
weakenType (lit l)      p = lit l

weakenTypes : ∀ {κs Σ₁ Σ₂} → Types Σ₁ κs → (p : Σ₁ ⊆ Σ₂) → Types Σ₂ κs
weakenTypes xs p = mapAll (λ τ → weakenType τ p) xs

weakenCxt : ∀ {Σ₁ Σ₂} → Cxt Σ₁ → Σ₁ ⊆ Σ₂ → Cxt Σ₂
weakenCxt τs p = map (flip weakenType p) τs

shift : ∀ {κ κ′ Σ} → Type Σ κ → Type (κ′ ∷ Σ) κ
shift τ = weakenType τ (⊆-skip ⊆-refl)

ShiftS : ∀ {Σ₁ Σ₂ κ} → TySubst Σ₁ Σ₂ → TySubst Σ₁ (κ ∷ Σ₂)
ShiftS = mapAll shift

LiftS : ∀ {Σ₁ Σ₂ κ} → TySubst Σ₁ Σ₂ → TySubst (κ ∷ Σ₁) (κ ∷ Σ₂)
LiftS sub = tvar hd ∷ ShiftS sub

LiftS-n : ∀ {Σ₁ Σ₂} Σ₃ → TySubst Σ₁ Σ₂ → TySubst (Σ₃ ++ Σ₁) (Σ₃ ++ Σ₂)
LiftS-n [] sub = sub
LiftS-n (_ ∷ Σ₃) sub = LiftS (LiftS-n Σ₃ sub)

lookupTySubst : ∀ {Σ₁ Σ₂ κ} → TySubst Σ₁ Σ₂ → κ ∈ Σ₁ → Type Σ₂ κ
lookupTySubst = ∈-All

applyTySubst : ∀ {Σ₁ Σ₂ κ} → TySubst Σ₁ Σ₂ → Type Σ₁ κ → Type Σ₂ κ
applyTySubst sub (tvar x) = lookupTySubst sub x
applyTySubst sub (τ₁ $ τ₂) = applyTySubst sub τ₁ $ applyTySubst sub τ₂
applyTySubst sub (τ₁ ⇒ τ₂) = applyTySubst sub τ₁ ⇒ applyTySubst sub τ₂
applyTySubst sub (forAll κ τ) = forAll κ (applyTySubst (LiftS sub) τ)
applyTySubst sub (con c) = con c
applyTySubst sub (lit l) = lit l

applyTySubst-ext : ∀ {Σ₁ Σ₂}  → (ps ps′ : TySubst Σ₁ Σ₂) →
  (∀ {κ} (x : κ ∈ Σ₁) → lookupTySubst ps x ≡ lookupTySubst ps′ x) →
  ∀ {κ} (τ : Type Σ₁ κ) → applyTySubst ps τ ≡ applyTySubst ps′ τ
applyTySubst-ext ps ps′ eq (tvar x) = eq x
applyTySubst-ext ps ps′ eq (τ $ τ₁) =
  cong₂ _$_ (applyTySubst-ext ps ps′ eq τ)
  (applyTySubst-ext ps ps′ eq τ₁)
applyTySubst-ext ps ps′ eq (τ ⇒ τ₁) =
  cong₂ _⇒_ (applyTySubst-ext ps ps′ eq τ)
    (applyTySubst-ext ps ps′ eq τ₁)
applyTySubst-ext {Σ₁} ps ps′ eq (forAll κ τ) =
  cong (forAll κ) (applyTySubst-ext (LiftS ps) (LiftS ps′) eq′ τ)
  where eq′ : ∀ {κ′} (x : κ′ ∈ (κ ∷ Σ₁)) → lookupTySubst (LiftS ps) x ≡ lookupTySubst (LiftS ps′) x
        eq′ hd = refl
        eq′ (tl x) = lookupTySubst (ShiftS ps) x
                       ≡⟨ ∈-mapAll shift ps x ⟩
                     shift (lookupTySubst ps x)
                       ≡⟨ cong shift (eq x) ⟩
                     shift (lookupTySubst ps′ x)
                       ≡⟨ ≡-sym (∈-mapAll shift ps′ x) ⟩
                     lookupTySubst (ShiftS ps′) x ∎
applyTySubst-ext ps ps′ eq (con x) = refl
applyTySubst-ext ps ps′ eq (lit x) = refl


ComposeS : ∀ {Σ₁ Σ₂ Σ₃} → TySubst Σ₁ Σ₂ → TySubst Σ₂ Σ₃ → TySubst Σ₁ Σ₃
ComposeS sub₁ sub₂ = mapAll (applyTySubst sub₂) sub₁

substTop : ∀ {Σ κ κ′} → Type Σ κ′ → Type (κ′ ∷ Σ) κ → Type Σ κ
substTop τ₁ τ₂ = applyTySubst (τ₁ ∷ IdS) τ₂

-- Eq instances

Adt-inj₁ : ∀ {κ} {ftc₁ ftc₂} {n₁ n₂} {cs₁ cs₂} →
             Adt {κ} ftc₁ n₁ cs₁ ≡ Adt {κ} ftc₂ n₂ cs₂ → ftc₁ ≡ ftc₂
Adt-inj₁ refl = refl

Adt-inj₂ : ∀ {κ} {ftc₁ ftc₂} {n₁ n₂} {cs₁ cs₂} →
             Adt {κ} ftc₁ n₁ cs₁ ≡ Adt {κ} ftc₂ n₂ cs₂ → n₁ ≡ n₂
Adt-inj₂ refl = refl

Adt-inj₃ : ∀ {κ} {ftc₁ ftc₂} {n} {cs₁ cs₂} →
             Adt {κ} ftc₁ n cs₁ ≡ Adt {κ} ftc₂ n cs₂ → cs₁ ≡ cs₂
Adt-inj₃ refl = refl


instance
  -- Avoid TERMINATING pragma by writing out the pattern matching
  EqKind : Eq Kind
  EqKind = record { _==_ = eq }
    where
      eq : (κ₁ κ₂ : Kind) → Dec (κ₁ ≡ κ₂)
      eq ∗ ∗ = yes refl
      eq ∗ (_ ⇒ _) = no (λ ())
      eq (_ ⇒ _) ∗ = no (λ ())
      eq (κ₁₁ ⇒ κ₁₂) (κ₂₁ ⇒ κ₂₂)
        = decEq₂ ⇒-inj₁ ⇒-inj₂ (eq κ₁₁ κ₂₁) (eq κ₁₂ κ₂₂)

  EqForeignTyCon : Eq ForeignTyCon
  EqForeignTyCon = record { _==_ = eq }
    where
      eq : unquote (deriveEqType (quote ForeignTyCon))
      unquoteDef eq = deriveEqDef (quote ForeignTyCon)

  EqForeignDataCon : Eq ForeignDataCon
  EqForeignDataCon = record { _==_ = eq }
    where
      eq : unquote (deriveEqType (quote ForeignDataCon))
      unquoteDef eq = deriveEqDef (quote ForeignDataCon)

  EqTyCon : ∀ {κ} → Eq (TyCon κ)

  {-# TERMINATING #-} -- Too much work to write it out manually
  EqType : ∀ {Σ κ} → Eq (Type Σ κ)
  EqType = record { _==_ = eq }
    where
      eq : unquote (deriveEqType (quote Type))
      unquoteDef eq = deriveEqDef (quote Type)

  EqADT : ∀ {κ} → Eq (ADT κ)
  EqADT = record { _==_ = eq }
    where
      eq : unquote (deriveEqType (quote ADT))
      eq (Adt ftc₁ n₁ cs₁) (Adt ftc₂ n₂ cs₂) with n₁ == n₂
      ... | no ¬p = no λ eq → ¬p (Adt-inj₂ eq)
      ... | yes p rewrite p = decEq₂ Adt-inj₁ Adt-inj₃
                                     (ftc₁ == ftc₂) (cs₁ == cs₂)

  EqTyCon = record { _==_ = eq }
    where
      eq : unquote (deriveEqType (quote TyCon))
      unquoteDef eq = deriveEqDef (quote TyCon)

  EqDataCon : ∀ {κ} {tc : TyCon κ} → Eq (DataCon tc)
  EqDataCon = record { _==_ = eq }
    where
      eq : unquote (deriveEqType (quote DataCon))
      unquoteDef eq = deriveEqDef (quote DataCon)


data ForeignLit (Σ : TyCxt) (τ : Type Σ ∗) : Set where
  flit : Literal → ForeignLit Σ τ

data ForeignVar (Σ : TyCxt) (τ : Type Σ ∗) : Set where
  fvar : Module → Ident → ForeignVar Σ τ

data ForeignDict (Σ : TyCxt) (τ : Type Σ ∗) : Set where
  fdict : ForeignDict Σ τ

lastAll : ∀ {A : Set} {P : A → Set} {xs : List A} {x : A} →
            All P (xs ++ x ∷ []) → All P xs × P x
lastAll {xs = []} (p ∷ []) = [] , p
lastAll {xs = x ∷ xs} (p ∷ all) with lastAll {xs = xs} all
... | all′ , p′ = (p ∷ all′) , p′

applyTyArgs : ∀ {Σ κ} → Type Σ κ → Types Σ (saturatedTyCxt κ) → Type Σ ∗
applyTyArgs {κ = ∗} τ [] = τ
applyTyArgs {Σ} {κ = κ ⇒ κ₁} τ τs with lastAll τs
... | τs′ , τ₁ = applyTyArgs (τ $ τ₁) τs′

tyConType : ∀ {κ} → (tc : TyCon κ) → Type (tyConCxt tc) ∗
tyConType tc = applyTyArgs (con tc) IdS

dcType : ∀ {κ} {tc : TyCon κ} → DataCon tc → Type [] ∗
dcType {κ} dc = mkForAll (ADT.tyCxt adt)
                         (mkFunRev (dataConArgs dc)
                                   (tyConType (con adt)))
  where
    adt : ADT κ
    adt = dataConADT dc



data Branch (Σ : TyCxt) (Γ : Cxt Σ) {κ} (adt : ADT κ)
            (tyArgs : Types Σ (ADT.tyCxt adt)) : Type Σ ∗ → Set

Exhaustive : ∀ {Σ} {Γ : Cxt Σ} {τ : Type Σ ∗} {κ} {adt : ADT κ} {tyArgs} →
               List (Branch Σ Γ {κ} adt tyArgs τ) → Set

infixl 4 _[_]

data Expr (Σ : TyCxt) (Γ : Cxt Σ) : Type Σ ∗ → Set where
  var     : ∀ {τ} → τ ∈ Γ → Expr Σ Γ τ
  _$_     : ∀ {τ₁ τ₂} → Expr Σ Γ (τ₁ ⇒ τ₂) → Expr Σ Γ τ₁ → Expr Σ Γ τ₂
  _[_]    : ∀ {κ τ₁} → Expr Σ Γ (forAll κ τ₁) → (τ₂ : Type Σ κ) →
              Expr Σ Γ (substTop τ₂ τ₁)
  lam     : ∀ τ₁ {τ₂} → Expr Σ (τ₁ ∷ Γ) τ₂ → Expr Σ Γ (τ₁ ⇒ τ₂)
  Λ       : ∀ κ {τ} → Expr (κ ∷ Σ) (weakenCxt Γ (⊆-skip ⊆-refl)) τ →
              Expr Σ Γ (forAll κ τ)
  con     : ∀ {κ} {tc : TyCon κ} → (dc : DataCon tc) →
              Expr Σ Γ (weakenType (dcType dc) [])
  lit     : ∀ {τ} → ForeignLit Σ τ → Expr Σ Γ τ
  fvar    : ∀ {τ} → ForeignVar Σ τ → Expr Σ Γ τ
  fdict   : ∀ {τ} → ForeignDict Σ τ → Expr Σ Γ τ -- TODO Constraint kind?
  match   : ∀ {τ} {κ} → (adt : ADT κ) → (tyArgs : Types Σ (ADT.tyCxt adt)) →
              Expr Σ Γ (applyTyArgs (con (con adt)) tyArgs) →
              (bs : List (Branch Σ Γ adt tyArgs τ)) →
              Exhaustive bs → Expr Σ Γ τ

data Pat (Σ : TyCxt) {κ} (adt : ADT κ) (tyArgs : Types Σ (ADT.tyCxt adt)) :
     Set where
  ̺   : Pat Σ adt tyArgs
  -- TODO unsafe: Literal can have another type
  lit : Literal → Pat Σ adt tyArgs
  con : (dc : DataCon (con adt)) → Pat Σ adt tyArgs

patBinders : ∀ {Σ κ} {adt : ADT κ} {tyArgs} → Pat Σ {κ} adt tyArgs → Cxt Σ
patBinders {tyArgs = tyArgs} (con dc) = map (applyTySubst tyArgs) (dataConArgs dc)
patBinders _ = []

data Branch Σ Γ {κ} adt tyArgs where
  alt : ∀ {τ} → (pat : Pat Σ adt tyArgs) →
          Expr Σ (patBinders pat +++ Γ) τ →
          Branch Σ Γ adt tyArgs τ

branchConstructorIndex : ∀ {Σ Γ κ adt tyArgs τ} → Branch Σ Γ {κ} adt tyArgs τ →
                           Maybe (Fin (ADT.nbConstructors adt))
branchConstructorIndex {adt = adt} (alt (con dc) _) = just (dataConIndex dc)
branchConstructorIndex _ = nothing

Exhaustive {adt = adt} bs
  = map just (allFin (ADT.nbConstructors adt))
  ≡ map branchConstructorIndex bs


-- TODO other typing rules on 13 of core-spec.pdf


--- Example ADT: Bool

BoolADT : ADT ∗
BoolADT = makeADT (fcon "GHC.Base" "Bool")
                  (((fcon "GHC.Base" "False") , []) ∷
                   ((fcon "GHC.Base" "True") , []) ∷ [])

`Bool` : TyCon ∗
`Bool` = con BoolADT

`False` : DataCon `Bool`
`False` = con BoolADT zero

`True` : DataCon `Bool`
`True` = con BoolADT (suc zero)



--- Example ADT: Maybe

MaybeADT : ADT (∗ ⇒ ∗)
MaybeADT = makeADT (fcon "Data.Maybe" "Maybe")
                   (((fcon "Data.Maybe" "Nothing") , []) ∷
                    ((fcon "Data.Maybe" "Just") , tvar hd ∷ []) ∷ [])

`Maybe` : TyCon (∗ ⇒ ∗)
`Maybe` = con MaybeADT


`Nothing` : DataCon `Maybe`
`Nothing` = con MaybeADT zero

`Just` : DataCon `Maybe`
`Just` = con MaybeADT (suc zero)


--- Try pattern matching
`not` : Expr [] [] (con `Bool` ⇒ con `Bool`)
`not` = lam (con `Bool`)
            (match BoolADT [] (var hd) (falseCase ∷ trueCase ∷ []) refl)
  where
    falseCase : Branch [] (con `Bool` ∷ []) BoolADT [] (con `Bool`)
    falseCase = alt (con `False`) (con `True`)
    trueCase : Branch [] (con `Bool` ∷ []) BoolADT [] (con `Bool`)
    trueCase = alt (con `True`) (con `False`)



--- Example ADT: List

{-# TERMINATING #-} -- TODO get rid of this?
`List` : TyCon (∗ ⇒ ∗)

ListADT : ADT (∗ ⇒ ∗)
ListADT = makeADT (fcon "GHC.Types" "[]")
                  (((fcon "GHC.Types" "[]") , []) ∷
                   ((fcon "GHC.Types" ":"), tvar hd ∷ (con `List` $ tvar hd) ∷ []) ∷ [])

`List` = con ListADT

`Nil` : DataCon `List`
`Nil` = con ListADT zero

`Cons` : DataCon `List`
`Cons` = con ListADT (suc zero)



`maybeToListBool` : Expr [] [] ((con `Maybe` $ con `Bool`) ⇒ (con `List` $ con `Bool`))
`maybeToListBool` = lam (con `Maybe` $ con `Bool`)
                         (match MaybeADT (con `Bool` ∷ []) (var hd)
                                (nothingCase ∷ justCase ∷ []) refl)
  where
    nothingCase : Branch [] ((con `Maybe` $ con `Bool`) ∷ [])
                             MaybeADT (con `Bool` ∷ []) (con `List` $ con `Bool`)
    nothingCase = alt (con `Nothing`) (con `Nil` [ _ ])
    justCase : Branch [] ((con `Maybe` $ con `Bool`) ∷ [])
                          MaybeADT (con `Bool` ∷ []) (con `List` $ con `Bool`)
    justCase = alt (con `Just`) (con `Cons` [ _ ] $ var hd $ con `Nil` [ _ ])



`maybeToList` : Expr [] [] (forAll ∗ (con `Maybe` $ tvar hd ⇒ con `List` $ tvar hd))
`maybeToList` = Λ ∗ (lam (con `Maybe` $ tvar hd)
                         (match MaybeADT (tvar hd ∷ []) (var hd)
                                (nothingCase ∷ justCase ∷ [])
                                refl))
  where
    nothingCase : Branch (∗ ∷ []) ((con `Maybe` $ tvar hd) ∷ [])
                         MaybeADT (tvar hd ∷ []) (con `List` $ tvar hd)
    nothingCase = alt (con `Nothing`)
                      (con `Nil` [ _ ])
    justCase : Branch (∗ ∷ []) ((con `Maybe` $ tvar hd) ∷ [])
                      MaybeADT (tvar hd ∷ []) (con `List` $ tvar hd)
    justCase = alt (con `Just`)
                   (con `Cons` [ _ ] $ var hd $ con `Nil` [ _ ])

--- Different cases of (G)ADTs to consider
{-


data Point where
  Point :: Int -> Int -> Point

data Maybe a where
  Just :: a -> Maybe a
  Nothing :: Maybe a

data Either a b where
  Left  :: a -> Either a b
  Right :: b -> Either a b

data List a where
  Nil :: List a
  Cons :: a -> List a -> List a

data Exists where
  Ex :: a -> Exists

data AShow
  AShow :: Show a => a -> AShow

data Expr t where
  Lit :: Int -> Expr Int
  Add :: Expr Int -> Expr Int -> Expr Int
  IsZero :: Expr Int -> Expr Bool

data Foo (a :: Bool) where
  T :: Foo True
  F :: Foo False

-}
