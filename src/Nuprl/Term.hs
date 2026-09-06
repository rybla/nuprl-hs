-- | Uniform term structure of NuPRL computational type theory.
--
-- A term is either a variable or an operator applied to a list of bound
-- subterms, matching the NuPRL 4 uniform syntax
--
-- > opid{p1:k1; ...; pm:km}(x1,...,xa1.t1; ...; xn,...,xan.tn)
--
-- Primitive type-theoretic constructors are exposed as bidirectional pattern
-- synonyms and smart constructors so the rest of the system never has to
-- manipulate raw operator identifiers.
module Nuprl.Term
  ( -- * Names
    Var (..)
  , mkVar
  , dummyVar
  , isHiddenVar
  , isDummyVar
  , OpId (..)
  , mkOpId
  , Name
    -- * Parameters and operators
  , ParamKind (..)
  , Parameter (..)
  , Operator (..)
  , mkOp
  , opArity
    -- * Universe levels
  , LevelExp (..)
  , levelVar
  , levelConst
  , levelAdd
  , levelMax
  , levelSucc
  , normalizeLevel
  , levelEq
  , levelLt
  , levelLe
  , prettyLevel
    -- * Terms
  , BoundTerm (..)
  , bterm
  , bterm0
  , bterm1
  , Term (..)
  , termOpId
  , termOperator
  , mapBound
    -- * Primitive operator identifiers
  , opUniverse
  , opVoid
  , opUnit
  , opAxiom
  , opInt
  , opNatural
  , opMinus
  , opAdd
  , opSubtract
  , opMultiply
  , opDivide
  , opRemainder
  , opIntEq
  , opLess
  , opAtom
  , opToken
  , opAtomEq
  , opLambda
  , opApply
  , opFunction
  , opPair
  , opSpread
  , opProduct
  , opInl
  , opInr
  , opDecide
  , opUnion
  , opEqual
  , opList
  , opNil
  , opCons
  , opListInd
  , opSet
  , opIsect
  , opSquash
  , opAny
  , opTrue
  , opFalse
  , opNot
  , opAnd
  , opOr
  , opImplies
  , opIff
  , opAll
  , opExists
  , opMember
  , opProp
    -- * Pattern synonyms
  , pattern TUniverse
  , pattern TVoid
  , pattern TUnit
  , pattern TAxiom
  , pattern TInt
  , pattern TNat
  , pattern TMinus
  , pattern TAdd
  , pattern TSub
  , pattern TMul
  , pattern TDiv
  , pattern TRem
  , pattern TIntEq
  , pattern TLess
  , pattern TAtom
  , pattern TToken
  , pattern TAtomEq
  , pattern TLambda
  , pattern TApply
  , pattern TFunction
  , pattern TPair
  , pattern TSpread
  , pattern TProduct
  , pattern TInl
  , pattern TInr
  , pattern TDecide
  , pattern TUnion
  , pattern TEqual
  , pattern TList
  , pattern TNil
  , pattern TCons
  , pattern TListInd
  , pattern TSet
  , pattern TIsect
  , pattern TSquash
  , pattern TAny
  , pattern TTrue
  , pattern TFalse
  , pattern TNot
  , pattern TAnd
  , pattern TOr
  , pattern TImplies
  , pattern TIff
  , pattern TAll
  , pattern TExists
  , pattern TMember
  , pattern TProp
    -- * Smart constructors
  , tUniverse
  , tVoid
  , tUnit
  , tAxiom
  , tInt
  , tNat
  , tMinus
  , tAdd
  , tSub
  , tMul
  , tDiv
  , tRem
  , tIntEq
  , tLess
  , tAtom
  , tToken
  , tAtomEq
  , tLambda
  , tApply
  , tApps
  , tFunction
  , tArrow
  , tPair
  , tSpread
  , tProduct
  , tTimes
  , tInl
  , tInr
  , tDecide
  , tUnion
  , tEqual
  , tMember
  , tList
  , tNil
  , tCons
  , tListInd
  , tSet
  , tIsect
  , tSquash
  , tAny
  , tTrue
  , tFalse
  , tNot
  , tAnd
  , tOr
  , tImplies
  , tIff
  , tAll
  , tExists
  , tProp
  , tOp0
  , tOp1
  , tOp2
    -- * Classification
  , isCanonicalType
  , isCanonicalValue
  , isSoftLogic
  , isDependentFun
  , isDependentProd
    -- * Uniform syntax
  , uniformTerm
  , uniformBound
  ) where

import Data.List (nub)
import Data.String (IsString (..))
import Data.Text (Text)
import Data.Text qualified as T
import GHC.Generics (Generic)

--------------------------------------------------------------------------------
-- Names
--------------------------------------------------------------------------------

-- | A binding or free variable. Variables whose name begins with @\'%\'@ are
-- /hidden/ (invisible in pretty-printing), matching NuPRL's convention.
newtype Var = Var {varText :: Text}
  deriving stock (Eq, Ord, Generic)
  deriving newtype (IsString)

instance Show Var where
  show (Var v) = T.unpack v

-- | Construct a variable. The empty name is the dummy\/null variable.
mkVar :: Text -> Var
mkVar = Var

-- | The null variable, which never binds.
dummyVar :: Var
dummyVar = Var T.empty

-- | Hidden variables start with @\'%\'@ and are suppressed in sequent display.
isHiddenVar :: Var -> Bool
isHiddenVar (Var v) = T.isPrefixOf "%" v

-- | The dummy\/null variable.
isDummyVar :: Var -> Bool
isDummyVar (Var v) = T.null v

-- | Operator identifier. An initial @\'!\'@ marks a system-language (non
-- object-language) operator, as in NuPRL 4.
newtype OpId = OpId {opIdText :: Text}
  deriving stock (Eq, Ord, Generic)
  deriving newtype (IsString)

instance Show OpId where
  show (OpId o) = T.unpack o

mkOpId :: Text -> OpId
mkOpId = OpId

-- | Library object name. Same lexical class as 'OpId'.
type Name = Text

--------------------------------------------------------------------------------
-- Parameters and operators
--------------------------------------------------------------------------------

-- | Parameter kinds of the uniform term language.
data ParamKind
  = KindNat
  | KindToken
  | KindString
  | KindVar
  | KindLevel
  deriving stock (Eq, Ord, Show, Generic)

-- | An operator parameter. Universe terms carry a 'LevelParam'; integer
-- literals carry a 'NatParam'.
data Parameter
  = NatParam Integer
  | TokenParam Text
  | StringParam Text
  | VarParam Var
  | LevelParam LevelExp
  deriving stock (Eq, Ord, Show, Generic)

-- | An operator is an identifier together with a (possibly empty) parameter
-- list.
data Operator = Operator
  { opId :: OpId
  , opParams :: [Parameter]
  }
  deriving stock (Eq, Ord, Show, Generic)

-- | Operator with no parameters.
mkOp :: OpId -> Operator
mkOp oid = Operator oid []

-- | Number of bound-term arguments of a term (its arity length, not the
-- individual binder counts).
opArity :: Term -> Int
opArity (TVar _) = 0
opArity (TOp _ bts) = length bts

--------------------------------------------------------------------------------
-- Universe levels
--------------------------------------------------------------------------------

-- | Universe level expressions, implicitly quantified over positive integers.
--
-- > L ::= v | k | L + n | max(L, L)
--
-- @L'@ in NuPRL notation is 'levelSucc'.
data LevelExp
  = -- | Level variable (implicitly ∀ over positive integers).
    LVar Text
  | -- | Positive integer constant.
    LConst Int
  | -- | @L + n@ with @n >= 0@.
    LAdd LevelExp Int
  | -- | Pointwise maximum.
    LMax LevelExp LevelExp
  deriving stock (Eq, Ord, Show, Generic)

levelVar :: Text -> LevelExp
levelVar = LVar

levelConst :: Int -> LevelExp
levelConst = LConst

-- | Add a non-negative increment, normalizing nested additions.
levelAdd :: LevelExp -> Int -> LevelExp
levelAdd e n
  | n <= 0 = e
  | otherwise = case e of
      LAdd e' m -> LAdd e' (m + n)
      LConst k -> LConst (k + n)
      _ -> LAdd e n

levelSucc :: LevelExp -> LevelExp
levelSucc e = levelAdd e 1

levelMax :: LevelExp -> LevelExp -> LevelExp
levelMax = LMax

-- | An atom of a normalized level: a constant, or a variable plus an offset.
data LevelAtom
  = LAConst Int
  | LAVar Text Int
  deriving stock (Eq, Ord, Show)

-- | Flatten a level into a list of atoms (the arguments of a top-level max).
normalizeLevel :: LevelExp -> [LevelAtom]
normalizeLevel = nub . go 0
  where
    go k = \case
      LConst n -> [LAConst (n + k)]
      LVar v -> [LAVar v k]
      LAdd e n -> go (k + n) e
      LMax a b -> go k a ++ go k b

-- | Drop atoms strictly dominated by another atom in the same list.
simplifyAtoms :: [LevelAtom] -> [LevelAtom]
simplifyAtoms as = filter (not . dominated) (nub as)
  where
    dominated a = any (\b -> b /= a && dominates b a) as
    dominates (LAVar v m) (LAVar w n) = v == w && m >= n
    dominates (LAConst m) (LAConst n) = m >= n
    dominates _ _ = False

atomLt :: LevelAtom -> LevelAtom -> Bool
atomLt (LAConst n) (LAConst m) = n < m
atomLt (LAVar v n) (LAVar w m) = v == w && n < m
atomLt _ _ = False

-- | Conservative equality of level expressions.
levelEq :: LevelExp -> LevelExp -> Bool
levelEq a b =
  simplifyAtoms (normalizeLevel a) == simplifyAtoms (normalizeLevel b)

-- | Conservative strict inequality. Returns 'True' only when the relation
-- holds for every valuation of level variables.
levelLt :: LevelExp -> LevelExp -> Bool
levelLt a b =
  let as = simplifyAtoms (normalizeLevel a)
      bs = simplifyAtoms (normalizeLevel b)
   in not (null as)
        && not (null bs)
        && all (\x -> any (atomLt x) bs) as

-- | Conservative non-strict inequality.
levelLe :: LevelExp -> LevelExp -> Bool
levelLe a b = levelEq a b || levelLt a b

prettyLevel :: LevelExp -> Text
prettyLevel = \case
  LVar v -> v
  LConst n -> T.pack (show n)
  LAdd e 1 -> prettyLevel e <> "'"
  LAdd e n -> prettyLevel e <> "+" <> T.pack (show n)
  LMax a b -> "max(" <> prettyLevel a <> "," <> prettyLevel b <> ")"

--------------------------------------------------------------------------------
-- Terms
--------------------------------------------------------------------------------

-- | A bound subterm @x1,...,xk.t@. The variables bind free occurrences in
-- 'btBody'.
data BoundTerm = BoundTerm
  { btVars :: [Var]
  , btBody :: Term
  }
  deriving stock (Eq, Ord, Show, Generic)

-- | Bound term with an arbitrary binder list.
bterm :: [Var] -> Term -> BoundTerm
bterm = BoundTerm

-- | Unbinding wrapper around a subterm.
bterm0 :: Term -> BoundTerm
bterm0 = BoundTerm []

-- | Single binder.
bterm1 :: Var -> Term -> BoundTerm
bterm1 x = BoundTerm [x]

-- | NuPRL terms. Variables are a dedicated constructor; the injection
-- @variable{x:v}()@ of the uniform syntax is implicit.
data Term
  = TVar Var
  | TOp Operator [BoundTerm]
  deriving stock (Eq, Ord, Generic)

instance Show Term where
  show = T.unpack . uniformTerm

termOperator :: Term -> Maybe Operator
termOperator (TOp op _) = Just op
termOperator TVar {} = Nothing

termOpId :: Term -> Maybe OpId
termOpId t = opId <$> termOperator t

-- | Map a function over the body of a bound term, preserving binders.
mapBound :: (Term -> Term) -> BoundTerm -> BoundTerm
mapBound f (BoundTerm vs t) = BoundTerm vs (f t)

--------------------------------------------------------------------------------
-- Operator identifiers
--------------------------------------------------------------------------------

opUniverse, opVoid, opUnit, opAxiom :: OpId
opUniverse = "universe"
opVoid = "void"
opUnit = "unit"
opAxiom = "axiom"

opInt, opNatural, opMinus, opAdd, opSubtract, opMultiply :: OpId
opInt = "int"
opNatural = "natural_number"
opMinus = "minus"
opAdd = "add"
opSubtract = "subtract"
opMultiply = "multiply"

opDivide, opRemainder, opIntEq, opLess :: OpId
opDivide = "divide"
opRemainder = "remainder"
opIntEq = "int_eq"
opLess = "less"

opAtom, opToken, opAtomEq :: OpId
opAtom = "atom"
opToken = "token"
opAtomEq = "atom_eq"

opLambda, opApply, opFunction :: OpId
opLambda = "lambda"
opApply = "apply"
opFunction = "function"

opPair, opSpread, opProduct :: OpId
opPair = "pair"
opSpread = "spread"
opProduct = "product"

opInl, opInr, opDecide, opUnion :: OpId
opInl = "inl"
opInr = "inr"
opDecide = "decide"
opUnion = "union"

opEqual :: OpId
opEqual = "equal"

opList, opNil, opCons, opListInd :: OpId
opList = "list"
opNil = "nil"
opCons = "cons"
opListInd = "list_ind"

opSet, opIsect, opSquash, opAny :: OpId
opSet = "set"
opIsect = "isect"
opSquash = "squash"
opAny = "any"

opTrue, opFalse, opNot, opAnd, opOr, opImplies, opIff :: OpId
opTrue = "true"
opFalse = "false"
opNot = "not"
opAnd = "and"
opOr = "or"
opImplies = "implies"
opIff = "iff"

opAll, opExists, opMember, opProp :: OpId
opAll = "all"
opExists = "exists"
opMember = "member"
opProp = "prop"

--------------------------------------------------------------------------------
-- Internal helpers for patterns
--------------------------------------------------------------------------------

op0 :: OpId -> Term
op0 oid = TOp (mkOp oid) []

op1 :: OpId -> Term -> Term
op1 oid a = TOp (mkOp oid) [bterm0 a]

op2 :: OpId -> Term -> Term -> Term
op2 oid a b = TOp (mkOp oid) [bterm0 a, bterm0 b]

--------------------------------------------------------------------------------
-- Pattern synonyms
--------------------------------------------------------------------------------

pattern TUniverse :: LevelExp -> Term
pattern TUniverse l = TOp (Operator (OpId "universe") [LevelParam l]) []

pattern TVoid :: Term
pattern TVoid = TOp (Operator (OpId "void") []) []

pattern TUnit :: Term
pattern TUnit = TOp (Operator (OpId "unit") []) []

pattern TAxiom :: Term
pattern TAxiom = TOp (Operator (OpId "axiom") []) []

pattern TInt :: Term
pattern TInt = TOp (Operator (OpId "int") []) []

pattern TNat :: Integer -> Term
pattern TNat n = TOp (Operator (OpId "natural_number") [NatParam n]) []

pattern TMinus :: Term -> Term
pattern TMinus a <- TOp (Operator (OpId "minus") []) [BoundTerm [] a]
  where
    TMinus a = TOp (mkOp opMinus) [bterm0 a]

pattern TAdd :: Term -> Term -> Term
pattern TAdd a b <- TOp (Operator (OpId "add") []) [BoundTerm [] a, BoundTerm [] b]
  where
    TAdd a b = op2 opAdd a b

pattern TSub :: Term -> Term -> Term
pattern TSub a b <- TOp (Operator (OpId "subtract") []) [BoundTerm [] a, BoundTerm [] b]
  where
    TSub a b = op2 opSubtract a b

pattern TMul :: Term -> Term -> Term
pattern TMul a b <- TOp (Operator (OpId "multiply") []) [BoundTerm [] a, BoundTerm [] b]
  where
    TMul a b = op2 opMultiply a b

pattern TDiv :: Term -> Term -> Term
pattern TDiv a b <- TOp (Operator (OpId "divide") []) [BoundTerm [] a, BoundTerm [] b]
  where
    TDiv a b = op2 opDivide a b

pattern TRem :: Term -> Term -> Term
pattern TRem a b <- TOp (Operator (OpId "remainder") []) [BoundTerm [] a, BoundTerm [] b]
  where
    TRem a b = op2 opRemainder a b

pattern TIntEq :: Term -> Term -> Term -> Term -> Term
pattern TIntEq a b t u <-
  TOp (Operator (OpId "int_eq") []) [BoundTerm [] a, BoundTerm [] b, BoundTerm [] t, BoundTerm [] u]
  where
    TIntEq a b t u =
      TOp (mkOp opIntEq) [bterm0 a, bterm0 b, bterm0 t, bterm0 u]

pattern TLess :: Term -> Term -> Term -> Term -> Term
pattern TLess a b t u <-
  TOp (Operator (OpId "less") []) [BoundTerm [] a, BoundTerm [] b, BoundTerm [] t, BoundTerm [] u]
  where
    TLess a b t u =
      TOp (mkOp opLess) [bterm0 a, bterm0 b, bterm0 t, bterm0 u]

pattern TAtom :: Term
pattern TAtom = TOp (Operator (OpId "atom") []) []

pattern TToken :: Text -> Term
pattern TToken s = TOp (Operator (OpId "token") [TokenParam s]) []

pattern TAtomEq :: Term -> Term -> Term -> Term -> Term
pattern TAtomEq a b t u <-
  TOp (Operator (OpId "atom_eq") []) [BoundTerm [] a, BoundTerm [] b, BoundTerm [] t, BoundTerm [] u]
  where
    TAtomEq a b t u =
      TOp (mkOp opAtomEq) [bterm0 a, bterm0 b, bterm0 t, bterm0 u]

pattern TLambda :: Var -> Term -> Term
pattern TLambda x b <- TOp (Operator (OpId "lambda") []) [BoundTerm [x] b]
  where
    TLambda x b = TOp (mkOp opLambda) [bterm1 x b]

pattern TApply :: Term -> Term -> Term
pattern TApply f a <- TOp (Operator (OpId "apply") []) [BoundTerm [] f, BoundTerm [] a]
  where
    TApply f a = op2 opApply f a

pattern TFunction :: Term -> Var -> Term -> Term
pattern TFunction a x b <-
  TOp (Operator (OpId "function") []) [BoundTerm [] a, BoundTerm [x] b]
  where
    TFunction a x b = TOp (mkOp opFunction) [bterm0 a, bterm1 x b]

pattern TPair :: Term -> Term -> Term
pattern TPair a b <- TOp (Operator (OpId "pair") []) [BoundTerm [] a, BoundTerm [] b]
  where
    TPair a b = op2 opPair a b

pattern TSpread :: Term -> Var -> Var -> Term -> Term
pattern TSpread p x y t <-
  TOp (Operator (OpId "spread") []) [BoundTerm [] p, BoundTerm [x, y] t]
  where
    TSpread p x y t = TOp (mkOp opSpread) [bterm0 p, BoundTerm [x, y] t]

pattern TProduct :: Term -> Var -> Term -> Term
pattern TProduct a x b <-
  TOp (Operator (OpId "product") []) [BoundTerm [] a, BoundTerm [x] b]
  where
    TProduct a x b = TOp (mkOp opProduct) [bterm0 a, bterm1 x b]

pattern TInl :: Term -> Term
pattern TInl a <- TOp (Operator (OpId "inl") []) [BoundTerm [] a]
  where
    TInl a = op1 opInl a

pattern TInr :: Term -> Term
pattern TInr a <- TOp (Operator (OpId "inr") []) [BoundTerm [] a]
  where
    TInr a = op1 opInr a

pattern TDecide :: Term -> Var -> Term -> Var -> Term -> Term
pattern TDecide d x t y u <-
  TOp
    (Operator (OpId "decide") [])
    [BoundTerm [] d, BoundTerm [x] t, BoundTerm [y] u]
  where
    TDecide d x t y u =
      TOp (mkOp opDecide) [bterm0 d, bterm1 x t, bterm1 y u]

pattern TUnion :: Term -> Term -> Term
pattern TUnion a b <- TOp (Operator (OpId "union") []) [BoundTerm [] a, BoundTerm [] b]
  where
    TUnion a b = op2 opUnion a b

pattern TEqual :: Term -> Term -> Term -> Term
pattern TEqual ty a b <-
  TOp (Operator (OpId "equal") []) [BoundTerm [] ty, BoundTerm [] a, BoundTerm [] b]
  where
    TEqual ty a b = TOp (mkOp opEqual) [bterm0 ty, bterm0 a, bterm0 b]

pattern TList :: Term -> Term
pattern TList a <- TOp (Operator (OpId "list") []) [BoundTerm [] a]
  where
    TList a = op1 opList a

pattern TNil :: Term
pattern TNil = TOp (Operator (OpId "nil") []) []

pattern TCons :: Term -> Term -> Term
pattern TCons h t <- TOp (Operator (OpId "cons") []) [BoundTerm [] h, BoundTerm [] t]
  where
    TCons h t = op2 opCons h t

pattern TListInd :: Term -> Term -> Var -> Var -> Var -> Term -> Term
pattern TListInd lst base x xs ih step <-
  TOp
    (Operator (OpId "list_ind") [])
    [BoundTerm [] lst, BoundTerm [] base, BoundTerm [x, xs, ih] step]
  where
    TListInd lst base x xs ih step =
      TOp (mkOp opListInd) [bterm0 lst, bterm0 base, BoundTerm [x, xs, ih] step]

pattern TSet :: Term -> Var -> Term -> Term
pattern TSet a x p <-
  TOp (Operator (OpId "set") []) [BoundTerm [] a, BoundTerm [x] p]
  where
    TSet a x p = TOp (mkOp opSet) [bterm0 a, bterm1 x p]

pattern TIsect :: Term -> Var -> Term -> Term
pattern TIsect a x b <-
  TOp (Operator (OpId "isect") []) [BoundTerm [] a, BoundTerm [x] b]
  where
    TIsect a x b = TOp (mkOp opIsect) [bterm0 a, bterm1 x b]

pattern TSquash :: Term -> Term
pattern TSquash a <- TOp (Operator (OpId "squash") []) [BoundTerm [] a]
  where
    TSquash a = op1 opSquash a

pattern TAny :: Term -> Term -> Term
pattern TAny v ty <- TOp (Operator (OpId "any") []) [BoundTerm [] v, BoundTerm [] ty]
  where
    TAny v ty = op2 opAny v ty

pattern TTrue :: Term
pattern TTrue = TOp (Operator (OpId "true") []) []

pattern TFalse :: Term
pattern TFalse = TOp (Operator (OpId "false") []) []

pattern TNot :: Term -> Term
pattern TNot a <- TOp (Operator (OpId "not") []) [BoundTerm [] a]
  where
    TNot a = op1 opNot a

pattern TAnd :: Term -> Term -> Term
pattern TAnd a b <- TOp (Operator (OpId "and") []) [BoundTerm [] a, BoundTerm [] b]
  where
    TAnd a b = op2 opAnd a b

pattern TOr :: Term -> Term -> Term
pattern TOr a b <- TOp (Operator (OpId "or") []) [BoundTerm [] a, BoundTerm [] b]
  where
    TOr a b = op2 opOr a b

pattern TImplies :: Term -> Term -> Term
pattern TImplies a b <-
  TOp (Operator (OpId "implies") []) [BoundTerm [] a, BoundTerm [] b]
  where
    TImplies a b = op2 opImplies a b

pattern TIff :: Term -> Term -> Term
pattern TIff a b <- TOp (Operator (OpId "iff") []) [BoundTerm [] a, BoundTerm [] b]
  where
    TIff a b = op2 opIff a b

pattern TAll :: Term -> Var -> Term -> Term
pattern TAll a x b <-
  TOp (Operator (OpId "all") []) [BoundTerm [] a, BoundTerm [x] b]
  where
    TAll a x b = TOp (mkOp opAll) [bterm0 a, bterm1 x b]

pattern TExists :: Term -> Var -> Term -> Term
pattern TExists a x b <-
  TOp (Operator (OpId "exists") []) [BoundTerm [] a, BoundTerm [x] b]
  where
    TExists a x b = TOp (mkOp opExists) [bterm0 a, bterm1 x b]

pattern TMember :: Term -> Term -> Term
pattern TMember t ty <-
  TOp (Operator (OpId "member") []) [BoundTerm [] t, BoundTerm [] ty]
  where
    TMember t ty = op2 opMember t ty

pattern TProp :: LevelExp -> Term
pattern TProp l = TOp (Operator (OpId "prop") [LevelParam l]) []

--------------------------------------------------------------------------------
-- Smart constructors
--------------------------------------------------------------------------------

tUniverse :: LevelExp -> Term
tUniverse = TUniverse

tVoid, tUnit, tAxiom, tInt, tAtom, tNil, tTrue, tFalse :: Term
tVoid = TVoid
tUnit = TUnit
tAxiom = TAxiom
tInt = TInt
tAtom = TAtom
tNil = TNil
tTrue = TTrue
tFalse = TFalse

tNat :: Integer -> Term
tNat = TNat

tMinus :: Term -> Term
tMinus = TMinus

tAdd, tSub, tMul, tDiv, tRem :: Term -> Term -> Term
tAdd = TAdd
tSub = TSub
tMul = TMul
tDiv = TDiv
tRem = TRem

tIntEq :: Term -> Term -> Term -> Term -> Term
tIntEq = TIntEq

tLess :: Term -> Term -> Term -> Term -> Term
tLess = TLess

tToken :: Text -> Term
tToken = TToken

tAtomEq :: Term -> Term -> Term -> Term -> Term
tAtomEq = TAtomEq

tLambda :: Var -> Term -> Term
tLambda = TLambda

tApply :: Term -> Term -> Term
tApply = TApply

-- | Left-associated chain of applications.
tApps :: Term -> [Term] -> Term
tApps = foldl TApply

tFunction :: Var -> Term -> Term -> Term
tFunction x a b = TFunction a x b

-- | Non-dependent function type @A → B@.
tArrow :: Term -> Term -> Term
tArrow a b = TFunction a dummyVar b

tPair :: Term -> Term -> Term
tPair = TPair

tSpread :: Var -> Var -> Term -> Term -> Term
tSpread x y p t = TSpread p x y t

tProduct :: Var -> Term -> Term -> Term
tProduct x a b = TProduct a x b

-- | Non-dependent product @A × B@.
tTimes :: Term -> Term -> Term
tTimes a b = TProduct a dummyVar b

tInl, tInr :: Term -> Term
tInl = TInl
tInr = TInr

tDecide :: Var -> Var -> Term -> Term -> Term -> Term
tDecide x y d t u = TDecide d x t y u

tUnion :: Term -> Term -> Term
tUnion = TUnion

tEqual :: Term -> Term -> Term -> Term
tEqual = TEqual

tMember :: Term -> Term -> Term
tMember = TMember

tList :: Term -> Term
tList = TList

tCons :: Term -> Term -> Term
tCons = TCons

tListInd :: Var -> Var -> Var -> Term -> Term -> Term -> Term
tListInd x xs ih lst base step = TListInd lst base x xs ih step

tSet :: Var -> Term -> Term -> Term
tSet x a p = TSet a x p

tIsect :: Var -> Term -> Term -> Term
tIsect x a b = TIsect a x b

tSquash :: Term -> Term
tSquash = TSquash

tAny :: Term -> Term -> Term
tAny = TAny

tNot :: Term -> Term
tNot = TNot

tAnd, tOr, tImplies, tIff :: Term -> Term -> Term
tAnd = TAnd
tOr = TOr
tImplies = TImplies
tIff = TIff

tAll :: Var -> Term -> Term -> Term
tAll x a b = TAll a x b

tExists :: Var -> Term -> Term -> Term
tExists x a b = TExists a x b

tProp :: LevelExp -> Term
tProp = TProp

tOp0 :: OpId -> Term
tOp0 = op0

tOp1 :: OpId -> Term -> Term
tOp1 = op1

tOp2 :: OpId -> Term -> Term -> Term
tOp2 = op2

--------------------------------------------------------------------------------
-- Classification
--------------------------------------------------------------------------------

-- | Canonical type formers (weak-head). Soft logic encodings are not
-- canonical; unfold them first.
isCanonicalType :: Term -> Bool
isCanonicalType = \case
  TUniverse {} -> True
  TVoid -> True
  TUnit -> True
  TInt -> True
  TAtom -> True
  TFunction {} -> True
  TProduct {} -> True
  TUnion {} -> True
  TEqual {} -> True
  TList {} -> True
  TSet {} -> True
  TIsect {} -> True
  TSquash {} -> True
  _ -> False

-- | Canonical values (weak-head).
isCanonicalValue :: Term -> Bool
isCanonicalValue = \case
  TAxiom -> True
  TNat _ -> True
  TToken _ -> True
  TLambda {} -> True
  TPair {} -> True
  TInl {} -> True
  TInr {} -> True
  TNil -> True
  TCons {} -> True
  TUniverse {} -> True
  t -> isCanonicalType t

-- | Soft logic encodings, treated as transparent by tactics.
isSoftLogic :: Term -> Bool
isSoftLogic = \case
  TTrue -> True
  TFalse -> True
  TNot {} -> True
  TAnd {} -> True
  TOr {} -> True
  TImplies {} -> True
  TIff {} -> True
  TAll {} -> True
  TExists {} -> True
  TMember {} -> True
  TProp {} -> True
  _ -> False

-- | Dependent function: the bound variable occurs free in the codomain.
isDependentFun :: Term -> Bool
isDependentFun (TFunction _ x b) = not (isDummyVar x) && x `freeIn` b
isDependentFun _ = False

isDependentProd :: Term -> Bool
isDependentProd (TProduct _ x b) = not (isDummyVar x) && x `freeIn` b
isDependentProd _ = False

-- Local free-in check so Term does not depend on Subst.
freeIn :: Var -> Term -> Bool
freeIn v = go
  where
    go (TVar x) = x == v
    go (TOp _ bts) = any goB bts
    goB (BoundTerm vs t) = v `notElem` vs && go t

--------------------------------------------------------------------------------
-- Uniform syntax (for debugging and Show)
--------------------------------------------------------------------------------

uniformTerm :: Term -> Text
uniformTerm (TVar v) = "variable{" <> varText v <> ":v}()"
uniformTerm (TOp (Operator oid params) bts) =
  opIdText oid <> paramsDoc <> "(" <> btermsDoc <> ")"
  where
    paramsDoc
      | null params = T.empty
      | otherwise =
          "{"
            <> T.intercalate "; " (map uniformParam params)
            <> "}"
    btermsDoc = T.intercalate "; " (map uniformBound bts)

uniformBound :: BoundTerm -> Text
uniformBound (BoundTerm vs t) =
  binders <> uniformTerm t
  where
    binders
      | null vs = T.empty
      | otherwise = T.intercalate "," (map varText vs) <> "."

uniformParam :: Parameter -> Text
uniformParam = \case
  NatParam n -> T.pack (show n) <> ":n"
  TokenParam s -> s <> ":t"
  StringParam s -> s <> ":s"
  VarParam v -> varText v <> ":v"
  LevelParam l -> prettyLevel l <> ":l"
