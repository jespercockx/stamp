module TypedCore where

open import MyPrelude hiding (_$_; [_])
open import CoreSyn
  hiding (module Type; module Expr; Expr)
  renaming (Kind to CKind; Type to CType; TyCon to CTyCon; DataCon to CDataCon)

data Kind : Set where
  ∗   : Kind
  _⇒_ : Kind → Kind → Kind


Context : Set → Set
Context = List

TyCxt : Set
TyCxt = Context Kind

data TyCon (κ : Kind) : Set where
  con : CTyCon → TyCon κ


data ForeignTy (κ : Kind) : Set where
  lit : TyLit → ForeignTy κ
  var : NameSpace → String → String → ForeignTy κ

infixr 2 _⇒_

infixl 3 _$_

data Type (Σ : TyCxt) : Kind → Set where
  var     : ∀ {κ} → κ ∈ Σ → Type Σ κ
  _$_     : ∀ {κ₁ κ₂} → Type Σ (κ₁ ⇒ κ₂) → Type Σ κ₁ → Type Σ κ₂
  _⇒_     : Type Σ ∗ → Type Σ ∗ → Type Σ ∗
  forAll  : ∀ κ → Type (κ ∷ Σ) ∗ → Type Σ ∗
  con     : ∀ {κ} → TyCon κ → Type Σ κ
  foreign : ∀ {κ} → ForeignTy κ → Type Σ κ


Cxt : TyCxt → Set
Cxt Σ = Context (Type Σ ∗)

--- Weakening and substitution

weakenType : ∀ {Σ₁ Σ₂ κ} → Type Σ₁ κ → Σ₁ ⊆ Σ₂ → Type Σ₂ κ
weakenType (var i)      p = var (∈-over-⊆ p i)
weakenType (τ₁ $ τ₂)    p = weakenType τ₁ p $ weakenType τ₂ p
weakenType (τ₁ ⇒ τ₂)    p = weakenType τ₁ p ⇒ weakenType τ₂ p
weakenType (forAll κ τ) p = forAll κ (weakenType τ (⊆-keep p))
weakenType (con c)      p = con c
weakenType (foreign f)  p = foreign f

weakenCxt : ∀ {Σ₁ Σ₂} → Cxt Σ₁ → Σ₁ ⊆ Σ₂ → Cxt Σ₂
weakenCxt [] _ = []
weakenCxt (τ :: τs) p = weakenType τ p :: weakenCxt τs p

shift : ∀ {κ κ′ Σ} → Type Σ κ → Type (κ′ ∷ Σ) κ
shift τ = weakenType τ (⊆-skip ⊆-refl)

{-# TERMINATING #-}
substTop : ∀ {Σ κ κ′} → Type Σ κ′ → Type (κ′ ∷ Σ) κ → Type Σ κ
substTop τ (var hd)     = τ
substTop τ (var (tl x)) = var x
substTop τ (t₁ $ t₂)    = substTop τ t₁ $ substTop τ t₂
substTop τ (t₁ ⇒ t₂)    = substTop τ t₁ ⇒ substTop τ t₂
substTop τ (forAll κ t) = forAll κ (substTop (weakenType τ (⊆-skip ⊆-refl))
                                             (weakenType t ⊆-swap))
substTop τ (con c)      = con c
substTop τ (foreign f)  = foreign f

--- Expr and related data types

data DataCon {Σ} (τ : Type Σ ∗) : Set where
  con : ∀ {κ} → CDataCon → (tc : TyCon κ) → DataCon τ

data ForeignExpr (Σ : TyCxt) (τ : Type Σ ∗) : Set where
  lit  : Literal → ForeignExpr Σ τ
  var  : NameSpace → String → String → ForeignExpr Σ τ
  dict : ForeignExpr Σ τ


data Branch (Σ : TyCxt) (Γ : Cxt Σ) : Type Σ ∗ → Type Σ ∗ → Set

data Expr (Σ : TyCxt) (Γ : Cxt Σ) : Type Σ ∗ → Set where
  var     : ∀ {τ} → τ ∈ Γ → Expr Σ Γ τ
  _$_     : ∀ {τ₁ τ₂} → Expr Σ Γ (τ₁ ⇒ τ₂) → Expr Σ Γ τ₁ → Expr Σ Γ τ₂
  _[_]    : ∀ {κ τ₁} → Expr Σ Γ (forAll κ τ₁) → (τ₂ : Type Σ κ) →
            Expr Σ Γ (substTop τ₂ τ₁)
  lam     : ∀ τ₁ {τ₂} → Expr Σ (τ₁ :: Γ) τ₂ → Expr Σ Γ (τ₁ ⇒ τ₂)
  Λ       : ∀ κ {τ} → Expr (κ :: Σ) (weakenCxt Γ (⊆-skip ⊆-refl)) τ →
            Expr Σ Γ (forAll κ τ)
  con     : ∀ {τ} → DataCon τ → Expr Σ Γ τ
  foreign : ∀ {τ} → ForeignExpr Σ τ → Expr Σ Γ τ
  match   : ∀ {τ₁ τ₂} → Expr Σ Γ τ₁ → List (Branch Σ Γ τ₁ τ₂) → Expr Σ Γ τ₂

  -- Case  : Expr b → b → Type → List (Alt b) → Expr b

data Pat {Σ : TyCxt} : Type Σ ∗ → Set where
  ̺   : ∀ {τ} → Pat {Σ} τ
  -- TODO unsafe: Literal can have another type
  lit : ∀ {τ} → Literal → Pat {Σ} τ
  -- TODO unsafe: DataCon can have another type
  con : ∀ {τ} → DataCon τ → Pat {Σ} τ

data Branch Σ Γ where
  alt : ∀ {τ₁ τ₂} → Pat {Σ} τ₁ → Expr Σ Γ τ₂ → Branch Σ Γ τ₁ τ₂


--- Utilities for modelling Algebraic Data Types

mkKind : TyCxt → Kind
mkKind [] = ∗
mkKind (κ ∷ Σ) = κ ⇒ mkKind Σ

mkFun : {Σ : TyCxt} → Cxt Σ → Type Σ ∗ → Type Σ ∗
mkFun []       τ = τ
mkFun (τ₁ ∷ Γ) τ = mkFun Γ (τ₁ ⇒ τ)

data Saturates : TyCxt → Kind → Set where
  []  : Saturates [] ∗
  _∷_ : ∀ {κ Σ} → (κ₁ : Kind) → Saturates Σ κ → Saturates (κ₁ ∷ Σ) (κ₁ ⇒ κ)

saturateTyCon : ∀ {Σ κ} → Saturates Σ κ → Type Σ κ → Type Σ ∗
saturateTyCon = go ⊆-refl
  where
    go : ∀ {Σ Σ′ κ} → Σ ⊆ Σ′ → Saturates Σ κ → Type Σ′ κ → Type Σ′ ∗
    go _ [] τ = τ
    go p (κ₁ ∷ sat) τ = go (λ z → p (tl z)) sat (τ $ var (p hd))

--- ADT

record ADT {n : Nat} {Σ : TyCxt} : Set where
  κ : Kind
  κ = mkKind Σ

  field
    tyArgs : Saturates Σ κ
    coreTyCon : CTyCon

  tyCon : TyCon κ
  tyCon = con coreTyCon

  field
    constructors : Vec (CDataCon × Cxt Σ) n

  unsaturatedTy : Type Σ κ
  unsaturatedTy = con tyCon

  saturatedTy : Type Σ ∗
  saturatedTy = saturateTyCon tyArgs (con tyCon)

open ADT {{...}} public



constructorType : ∀ {n Σ} → (adt : ADT {n} {Σ}) → Fin n → Type Σ ∗
constructorType adt i with indexVec (ADT.constructors adt) i
... | _ , args = mkFun args (ADT.saturatedTy adt)

constructorDataCon : ∀ {n Σ} → (adt : ADT {n} {Σ}) → (i : Fin n) →
                       DataCon (constructorType adt i)
constructorDataCon adt i with indexVec (ADT.constructors adt) i
... | dc , _ = con dc (ADT.tyCon adt)

constructorExpr : ∀ {n Σ} → (adt : ADT {n} {Σ}) → (i : Fin n) →
                    Expr Σ [] (constructorType adt i)
constructorExpr adt i = con (constructorDataCon adt i)


--- Example: Bool

BoolADT : ADT
BoolADT
  = record { tyArgs       = []
           ; coreTyCon    = boolTyCon
           ; constructors = (trueDataCon , []) ∷ (falseDataCon , []) ∷ []
           }

`Bool` : Type [] ∗
`Bool` = ADT.unsaturatedTy BoolADT

`True` : DataCon `Bool`
`True` = constructorDataCon BoolADT zero

`False` : DataCon `Bool`
`False` = constructorDataCon BoolADT (suc zero)


--- Example: Maybe
postulate
  maybeTyCon     : CTyCon
  justDataCon    : CDataCon
  nothingDataCon : CDataCon


MaybeADT : ADT
MaybeADT
  = record { tyArgs       = ∗ ∷ []
           ; coreTyCon    = maybeTyCon
           ; constructors = (nothingDataCon , []) ∷
                            (justDataCon , var hd ∷ []) ∷
                            []
           }

`Maybe` : Type (∗ ∷ []) (∗ ⇒ ∗)
`Maybe` = ADT.unsaturatedTy MaybeADT

`Nothing` : Expr (∗ ∷ []) [] (`Maybe` $ var hd)
`Nothing` = constructorExpr MaybeADT zero

`Just` : Expr (∗ ∷ []) [] (var hd ⇒ `Maybe` $ var hd)
`Just` = constructorExpr MaybeADT (suc zero)

--- Try pattern matching


`not` : Expr [] [] (`Bool` ⇒ `Bool`)
`not` = lam `Bool` (match (var hd) (trueCase ∷ falseCase ∷ []))
  where
    trueCase : Branch [] (`Bool` ∷ []) `Bool` `Bool`
    trueCase = alt (con `True`) (con `False`)
    falseCase : Branch [] (`Bool` ∷ []) `Bool` `Bool`
    falseCase = alt (con `False`) (con `True`)

-- TODO check exhaustiveness


--- Once useful helpers and test cases

ex₁ : ∀ {Σ Γ} → Expr Σ Γ (forAll ∗ (var hd ⇒ var hd))
ex₁ = Λ ∗ (lam (var hd) (var hd))


-- tyCon : ∀ {κ} {Σ} → Type Σ κ → Maybe (∃ λ κ′ → TyCon κ′)
-- tyCon      (τ $ _)  = tyCon τ
-- tyCon {κ′} (con tc) = just (κ′ , tc)
-- tyCon      _        = nothing

resType : ∀ {Σ} → Type Σ ∗ → ∃ λ Σ′ → Type Σ′ ∗
resType (_ ⇒ τ)      = resType τ
resType (forAll κ τ) = resType τ
resType {Σ} τ        = Σ , τ

argTypes : ∀ {Σ} → Type Σ ∗ → ∃ λ Σ′ → List (Type (Σ′ ++ Σ) ∗)
argTypes {Σ} (forAll κ τ) with argTypes τ
... | Σ′ , τs rewrite (cons-middle-snoc {y = κ} Σ′ Σ) = Σ′ ++ (κ ∷ []) , τs
argTypes (τ₁ ⇒ τ₂) with argTypes τ₂
... | Σ′ , τs = Σ′ , weakenType τ₁ (∈-prefix {ys = Σ′}) ∷ τs
argTypes τ = [] , []

-- foo : Type [] ∗
-- foo = forAll (∗ ⇒ ∗) (forAll ∗ (var hd ⇒ var (tl hd) $ var hd))


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
