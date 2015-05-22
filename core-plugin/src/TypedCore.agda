module TypedCore where

{-# IMPORT TysWiredIn #-}

open import Data.List using (All; _∷_; []) public
open import MyPrelude hiding (_$_; [_])
open import CoreSyn
  hiding (module Type; module Expr; Expr; TyCon; DataCon)
  renaming (Kind to CKind; Type to CType)

data Kind : Set where
  ∗   : Kind
  _⇒_ : Kind → Kind → Kind


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
-- More efficient alternative:
--
--     satTyCxt : ∀ {κ} → Saturates κ → TyCxt
--     satTyCxt = reverse ∘ convert
--       where
--         convert : ∀ {κ} → Saturates κ → TyCxt
--         convert [] = []
--         convert (κ ∷ sat) = κ ∷ convert sat
--
-- However, `satTyCxt-⊆` becomes much harder to prove.

saturatedTyCxt : ∀ κ → TyCxt
saturatedTyCxt = satTyCxt ∘ saturate


satTyCxt-⊆ : ∀ {κ κₛ} → (sat : Saturates κₛ) → satTyCxt sat ⊆ satTyCxt (κ ∷ sat)
satTyCxt-⊆ sat p = ∈-suffix p

-- Saturates the type with kind κ using the types stored in the contexts
--
-- Examples:
--
--     postulate
--       t₁ : Type ((∗ ⇒ ∗ ⇒ ∗) ∷ (∗ ⇒ ∗) ∷ []) ((∗ ⇒ ∗) ⇒ (∗ ⇒ ∗ ⇒ ∗) ⇒ ∗)
--       MaybeT : Type (∗ ∷ (∗ ⇒ ∗) ∷ []) ((∗ ⇒ ∗) ⇒ ∗ ⇒ ∗)
--     saturateType t₁ ≡ t₁ $ var (tl hd) $ var hd
--     saturateType MaybeT = MaybeT $ var (tl hd) $ var hd
--
saturateType : ∀ {κ} → Type (saturatedTyCxt κ) κ → Type (saturatedTyCxt κ) ∗
saturateType {κ} = go (saturate κ) ⊆-refl
  where
    go : ∀ {Σ κ} → (sat : Saturates κ) → satTyCxt sat ⊆ Σ → Type Σ κ → Type Σ ∗
    go []         _ τ = τ
    go (κ₁ ∷ sat) p τ
       = go sat (⊆-trans (satTyCxt-⊆ sat) p)
                (τ $ tvar (∈-over-⊆ p (∈-++-suffix {ys = satTyCxt sat} hd)))

data ForeignTyCon : Set where
  fcon : Module → Ident → ForeignTyCon

data ForeignDataCon : Set where
  fcon : Module → Ident → ForeignDataCon

data TyCon κ where
  con : ForeignTyCon → List ForeignDataCon → TyCon κ

tyConArgs : ∀ {κ} → TyCon κ → TyCxt
tyConArgs {κ} _ = saturatedTyCxt κ

tyConType : ∀ {κ} → (tc : TyCon κ) → Type (tyConArgs tc) ∗
tyConType tc = saturateType (con tc)

tyConConstructors : ∀ {κ} → TyCon κ → List ForeignDataCon
tyConConstructors (con _ cs) = cs

--- Weakening and substitution

weakenType : ∀ {Σ₁ Σ₂ κ} → Type Σ₁ κ → Σ₁ ⊆ Σ₂ → Type Σ₂ κ
weakenType (tvar i)     p = tvar (∈-over-⊆ p i)
weakenType (τ₁ $ τ₂)    p = weakenType τ₁ p $ weakenType τ₂ p
weakenType (τ₁ ⇒ τ₂)    p = weakenType τ₁ p ⇒ weakenType τ₂ p
weakenType (forAll κ τ) p = forAll κ (weakenType τ (⊆-keep p))
weakenType (con c)      p = con c
weakenType (lit l)      p = lit l

weakenCxt : ∀ {Σ₁ Σ₂} → Cxt Σ₁ → Σ₁ ⊆ Σ₂ → Cxt Σ₂
weakenCxt [] _ = []
weakenCxt (τ :: τs) p = weakenType τ p :: weakenCxt τs p

shift : ∀ {κ κ′ Σ} → Type Σ κ → Type (κ′ ∷ Σ) κ
shift τ = weakenType τ (⊆-skip ⊆-refl)

{-# TERMINATING #-}
substTop : ∀ {Σ κ κ′} → Type Σ κ′ → Type (κ′ ∷ Σ) κ → Type Σ κ
substTop τ (tvar hd)     = τ
substTop τ (tvar (tl x)) = tvar x
substTop τ (t₁ $ t₂)     = substTop τ t₁ $ substTop τ t₂
substTop τ (t₁ ⇒ t₂)     = substTop τ t₁ ⇒ substTop τ t₂
substTop τ (forAll κ t)  = forAll κ (substTop (weakenType τ (⊆-skip ⊆-refl))
                                             (weakenType t ⊆-swap))
substTop τ (con c)       = con c
substTop τ (lit l)       = lit l

--- Expr and related data types

_constrOf_ : ∀ {κ} → ForeignDataCon → TyCon κ → Set
cdc constrOf (con _ cdcs) = cdc ∈ cdcs

infixr 5 _+++_

-- [1, 2] +++ [3, 4] = [2, 1, 3, 4]
_+++_ : ∀ {A : Set} → List A → List A → List A
[] +++ ys = ys
(x ∷ xs) +++ ys = xs +++ x ∷ ys

mkForAll : ∀ (Σ : TyCxt) → Type Σ ∗ → Type [] ∗
mkForAll [] τ = τ
mkForAll (κ ∷ Σ) τ = mkForAll Σ (forAll κ τ)


mkFun : ∀ {Σ : TyCxt} → Cxt Σ → Type Σ ∗ → Type Σ ∗
mkFun []       τ = τ
mkFun (τ₁ ∷ Γ) τ = τ₁ ⇒ mkFun Γ τ

-- TODO IDEA: use records for a number of types to avoid all these
-- extra selectors?
data DataCon {κ} : TyCon κ → Set where
  con : ∀ (cdc : ForeignDataCon) →
          (tc : TyCon κ) →
          cdc constrOf tc →
          (args : Cxt (tyConArgs tc)) →
          DataCon tc

dcType : ∀ {κ} {tc : TyCon κ} → DataCon tc → Type [] ∗
dcType (con cdc tc x args) = mkForAll (tyConArgs tc) (mkFun args (tyConType tc))

dataConForeignDataCon : ∀ {κ} {tc : TyCon κ} → DataCon tc → ForeignDataCon
dataConForeignDataCon (con cdc _ _ _) = cdc

dataConName : ∀ {κ} {tc : TyCon κ} → DataCon tc → String
dataConName dc with dataConForeignDataCon dc
... | fcon _ name = name

data ForeignLit (Σ : TyCxt) (τ : Type Σ ∗) : Set where
  flit : Literal → ForeignLit Σ τ

data ForeignVar (Σ : TyCxt) (τ : Type Σ ∗) : Set where
  fvar : Module → Ident → ForeignVar Σ τ

data ForeignDict (Σ : TyCxt) (τ : Type Σ ∗) : Set where
  fdict : ForeignDict Σ τ

data Branch (Σ : TyCxt) (Γ : Cxt Σ) : Type Σ ∗ → Type Σ ∗ → Set

allConstructors : ∀ {κ Σ Γ τ₁ τ₂} → TyCon κ → List (Branch Σ Γ τ₁ τ₂) → Set

Exhaustive : ∀ {Σ} {Γ : Cxt Σ} {τ₁ τ₂ : Type Σ ∗} → List (Branch Σ Γ τ₁ τ₂) → Set
Exhaustive {τ₁ = τ₁} bs with typeTyCon τ₁
... | nothing = ⊥
... | just (_ , tc) = allConstructors tc bs

infixl 4 _[_]

data Expr (Σ : TyCxt) (Γ : Cxt Σ) : Type Σ ∗ → Set where
  var     : ∀ {τ} → τ ∈ Γ → Expr Σ Γ τ
  _$_     : ∀ {τ₁ τ₂} → Expr Σ Γ (τ₁ ⇒ τ₂) → Expr Σ Γ τ₁ → Expr Σ Γ τ₂
  _[_]    : ∀ {κ τ₁} → Expr Σ Γ (forAll κ τ₁) → (τ₂ : Type Σ κ) →
            Expr Σ Γ (substTop τ₂ τ₁)
  lam     : ∀ τ₁ {τ₂} → Expr Σ (τ₁ :: Γ) τ₂ → Expr Σ Γ (τ₁ ⇒ τ₂)
  Λ       : ∀ κ {τ} → Expr (κ :: Σ) (weakenCxt Γ (⊆-skip ⊆-refl)) τ →
            Expr Σ Γ (forAll κ τ)
  con     : ∀ {κ} {tc : TyCon κ} → (dc : DataCon tc) →
              Expr Σ Γ (weakenType (dcType dc) ⊆-empty)
  lit     : ∀ {τ} → ForeignLit Σ τ → Expr Σ Γ τ
  fvar    : ∀ {τ} → ForeignVar Σ τ → Expr Σ Γ τ
  fdict   : ∀ {τ} → ForeignDict Σ τ → Expr Σ Γ τ -- TODO Constraint kind?
  match   : ∀ {τ₁ τ₂} → Expr Σ Γ τ₁ → (bs : List (Branch Σ Γ τ₁ τ₂)) →
              -- TODO temp dummy proof
              1 ≡ 1 → Expr Σ Γ τ₂
              -- Exhaustive bs → Expr Σ Γ τ₂

Types : TyCxt → List Kind → Set
Types Σ = All (Type Σ)

weakenTypes : ∀ {κ κs Σ} → Types Σ κs → Types (κ ∷ Σ) κs
weakenTypes [] = []
weakenTypes (τ ∷ τs) = weakenType τ (⊆-skip ⊆-refl) ∷ weakenTypes τs

lastAll : ∀ {A : Set} {P : A → Set} {xs : List A} {x : A} →
            All P (xs ++ x ∷ []) → All P xs × P x
lastAll {xs = []} (p ∷ []) = [] , p
lastAll {xs = x ∷ xs} (p ∷ all) with lastAll {xs = xs} all
... | all′ , p′ = (p ∷ all′) , p′

applyTyArgs : ∀ {Σ κ} → Type Σ κ → Types Σ (saturatedTyCxt κ) → Type Σ ∗
applyTyArgs {κ = ∗} τ [] = τ
applyTyArgs {Σ} {κ = κ ⇒ κ₁} τ τs with lastAll τs
... | τs′ , τ₁ = applyTyArgs (τ $ τ₁) τs′


data Pat (Σ : TyCxt) : Type Σ ∗ → Set where
  ̺   : ∀ {τ} → Pat Σ τ
  -- TODO unsafe: Literal can have another type
  lit : ∀ {τ} → Literal → Pat Σ τ
  con : ∀ {κ} {tc : TyCon κ} → (tyArgs : Types Σ (tyConArgs tc)) →
          (dc : DataCon tc) → Pat Σ (applyTyArgs (con tc) tyArgs)

-- TODO name and intuition behind it
transplantVar : ∀ {κ Σ Σ′} → κ ∈ Σ → Types Σ′ Σ → Type Σ′ κ
transplantVar hd (τ ∷ _) = τ
transplantVar (tl n) (p ∷ τs) = transplantVar n τs

transplant : ∀ {κ Σ Σ′} → Types Σ′ Σ →
               Type Σ κ → Type Σ′ κ
transplant τs (tvar n)     = transplantVar n τs
transplant τs (τ₁ $ τ₂)    = transplant τs τ₁ $ transplant τs τ₂
transplant τs (τ₁ ⇒ τ₂)    = transplant τs τ₁ ⇒ transplant τs τ₂
transplant τs (forAll κ τ) = forAll κ (transplant (tvar hd ∷ weakenTypes τs) τ)
transplant τs (con c)      = con c
transplant τs (lit l)      = lit l


patBinders : ∀ {Σ τ} → Pat Σ τ → Cxt Σ
patBinders (con tyArgs (con _ tc _ args)) = map (transplant tyArgs) args
patBinders _ = []

data Branch Σ Γ where
  alt : ∀ {τ₁ τ₂} → (pat : Pat Σ τ₁) →
          Expr Σ (patBinders pat +++ Γ) τ₂ →
          Branch Σ Γ τ₁ τ₂

allConstructors tc branches
  = tyConConstructors tc ≡ mapMaybe extractForeignDataCon branches
  where
    extractForeignDataCon : ∀ {Σ Γ τ₁ τ₂} → Branch Σ Γ τ₁ τ₂ → Maybe ForeignDataCon
    extractForeignDataCon (alt (con _ dc) _) = just (dataConForeignDataCon dc)
    extractForeignDataCon _                  = nothing

-- TODO other typing rules on 13 of core-spec.pdf

--- Example ADT: Bool

trueDC : ForeignDataCon
trueDC = fcon "GHC.Base" "True"

falseDC : ForeignDataCon
falseDC = fcon "GHC.Base" "False"

`Bool` : TyCon ∗
`Bool` = con (fcon "GHC.Base" "Bool") (falseDC ∷ trueDC ∷ [])

`True` : DataCon `Bool`
`True` = con trueDC `Bool` (tl hd) []

`False` : DataCon `Bool`
`False` = con falseDC `Bool` hd []

--- Example ADT: Maybe

nothingDC : ForeignDataCon
nothingDC = fcon "Data.Maybe" "Nothing"

justDC : ForeignDataCon
justDC = fcon "Data.Maybe" "Just"

`Maybe` : TyCon (∗ ⇒ ∗)
`Maybe` = con (fcon "Data.Maybe" "Maybe") (nothingDC ∷ justDC ∷ [])

`Nothing` : DataCon `Maybe`
`Nothing` = con nothingDC `Maybe` hd []

`Just` : DataCon `Maybe`
`Just` = con justDC `Maybe` (tl hd) (tvar hd ∷ [])

--- Try pattern matching
`not` : Expr [] [] (con `Bool` ⇒ con `Bool`)
`not` = lam (con `Bool`)
            (match (var hd) (falseCase ∷ trueCase ∷ []) refl)
  where
    falseCase : Branch [] (con `Bool` ∷ []) (con `Bool`) (con `Bool`)
    falseCase = alt (con [] `False`) (con `True`)
    trueCase : Branch [] (con `Bool` ∷ []) (con `Bool`) (con `Bool`)
    trueCase = alt (con [] `True`) (con `False`)

--- Example ADT: List

nilDC : ForeignDataCon
nilDC = fcon "GHC.Types" "[]"

consDC : ForeignDataCon
consDC = fcon "GHC.Types" ":"

`List` : TyCon (∗ ⇒ ∗)
`List` = con (fcon "GHC.Types" "[]") (nilDC ∷ consDC ∷ [])

`Nil` : DataCon `List`
`Nil` = con nilDC `List` hd []

`Cons` : DataCon `List`
`Cons` = con consDC `List` (tl hd) (tvar hd ∷ (con `List` $ tvar hd) ∷ [])

`maybeToListBool` : Expr [] [] ((con `Maybe` $ con `Bool`) ⇒ (con `List` $ con `Bool`))
`maybeToListBool` = lam (con `Maybe` $ con `Bool`)
                         (match (var hd)
                                (nothingCase ∷ justCase ∷ []) refl)
  where
    nothingCase : Branch [] ((con `Maybe` $ con `Bool`) ∷ [])
                         (con `Maybe` $ con `Bool`) (con `List` $ con `Bool`)
    nothingCase = alt (con (con `Bool` ∷ []) `Nothing`)
                      (con `Nil` [ _ ])
    justCase : Branch [] ((con `Maybe` $ con `Bool`) ∷ [])
                      (con `Maybe` $ con `Bool`) (con `List` $ con `Bool`)
    justCase = alt (con (con `Bool` ∷ []) `Just`)
                   (con `Cons` [ _ ] $ var hd $ con `Nil` [ _ ])


`maybeToList` : Expr [] [] (forAll ∗ (con `Maybe` $ tvar hd ⇒ con `List` $ tvar hd))
`maybeToList` = Λ ∗ (lam (con `Maybe` $ tvar hd)
                         (match (var hd)
                                (nothingCase ∷ justCase ∷ [])
                                refl))
  where
    nothingCase : Branch (∗ ∷ []) ((con `Maybe` $ tvar hd) ∷ [])
                         (con `Maybe` $ tvar hd) (con `List` $ tvar hd)
    nothingCase = alt (con (tvar hd ∷ []) `Nothing`)
                      (con `Nil` [ _ ])
    justCase : Branch (∗ ∷ []) ((con `Maybe` $ tvar hd) ∷ [])
                      (con `Maybe` $ tvar hd) (con `List` $ tvar hd)
    justCase = alt (con (tvar hd ∷ []) `Just`)
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
