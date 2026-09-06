-- | The NuPRL library: a linear database of named objects, grouped into
-- theories (NuPRL §3).
--
-- Objects are theorems, abstractions, comments, and softness declarations.
-- A library is a pure value; loading a file is an IO wrapper around
-- 'importTheory'.
module Nuprl.Library
  ( Status (..)
  , statusChar
  , Abstraction (..)
  , Theorem (..)
  , Object (..)
  , objectKind
  , Theory (..)
  , Library (..)
  , emptyLibrary
  , coreLibrary
  , lookupObject
  , insertObject
  , lemmaEnv
  , unfoldAbs
  , setSoft
  , importTheory
  , libraryTheorems
  , prettyLibrary
  ) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T

import Nuprl.Error
import Nuprl.Pretty (renderTerm)
import Nuprl.Rule (AbsDef (..), LemmaEnv (..))
import Nuprl.Subst (substMany)
import Nuprl.Tactic (TacticExpr (..))
import Nuprl.Term

-- | Object status, matching NuPRL's library window (raw \/ bad \/ incomplete
-- \/ complete).
data Status
  = StatusRaw
  | StatusBad
  | StatusIncomplete
  | StatusComplete
  deriving stock (Eq, Ord, Show)

statusChar :: Status -> Char
statusChar = \case
  StatusRaw -> '?'
  StatusBad -> '-'
  StatusIncomplete -> '#'
  StatusComplete -> '*'

-- | An abstraction @opid(formals) == rhs@.
data Abstraction = Abstraction
  { absOpId :: OpId
  , absFormals :: [BoundTerm]
  , absRhs :: Term
  , absSoft :: Bool
  }
  deriving stock (Eq, Show)

-- | A theorem object: a goal together with a tactic script.
data Theorem = Theorem
  { thmGoal :: Term
  , thmScript :: TacticExpr
  , thmStatus :: Status
  , thmExtract :: Maybe Term
  }
  deriving stock (Eq, Show)

-- | A library object.
data Object
  = ObjTheorem Theorem
  | ObjAbs Abstraction
  | ObjComment Text
  | ObjSoft [Name]
  deriving stock (Eq, Show)

objectKind :: Object -> Char
objectKind = \case
  ObjTheorem _ -> 'T'
  ObjAbs _ -> 'A'
  ObjComment _ -> 'C'
  ObjSoft _ -> 'S'

-- | A theory is a named, ordered collection of objects plus import names.
data Theory = Theory
  { theoryName :: Name
  , theoryImports :: [Name]
  , theoryObjects :: [(Name, Object)]
  }
  deriving stock (Eq, Show)

-- | The in-memory library.
data Library = Library
  { libOrder :: [Name]
  , libObjects :: Map Name Object
  , libTheories :: Map Name Theory
  }
  deriving stock (Eq, Show)

emptyLibrary :: Library
emptyLibrary = Library [] Map.empty Map.empty

lookupObject :: Name -> Library -> Maybe Object
lookupObject n lib = Map.lookup n (libObjects lib)

insertObject :: Name -> Object -> Library -> Library
insertObject n obj lib =
  lib
    { libObjects = Map.insert n obj (libObjects lib)
    , libOrder =
        if n `elem` libOrder lib
          then libOrder lib
          else libOrder lib ++ [n]
    }

-- | Statements of complete theorems, for the refiner.
lemmaEnv :: Library -> LemmaEnv
lemmaEnv lib =
  LemmaEnv
    { unLemmaEnv =
        Map.mapMaybe
          ( \case
              ObjTheorem th | thmStatus th == StatusComplete -> Just (thmGoal th)
              _ -> Nothing
          )
          (libObjects lib)
    , unAbsEnv =
        Map.fromList
          [ (absOpId a, AbsDef (absFormals a) (absRhs a))
          | ObjAbs a <- Map.elems (libObjects lib)
          ]
    }

libraryTheorems :: Library -> [(Name, Theorem)]
libraryTheorems lib =
  [ (n, th)
  | n <- libOrder lib
  , ObjTheorem th <- maybe [] pure (lookupObject n lib)
  ]

-- | Mark named abstractions as soft.
setSoft :: [Name] -> Library -> Library
setSoft names lib =
  foldl
    ( \l n ->
        case lookupObject n l of
          Just (ObjAbs a) -> insertObject n (ObjAbs a {absSoft = True}) l
          _ -> l
    )
    lib
    names

-- | Unfold a user abstraction at the root, if the operator matches.
unfoldAbs :: Library -> Term -> Maybe Term
unfoldAbs lib (TOp (Operator oid _) bts) =
  case [a | ObjAbs a <- Map.elems (libObjects lib), absOpId a == oid] of
    abs_ : _
      | length (absFormals abs_) == length bts ->
          Just (instantiateAbs abs_ bts)
    _ -> Nothing
unfoldAbs _ _ = Nothing

instantiateAbs :: Abstraction -> [BoundTerm] -> Term
instantiateAbs abs_ bts =
  -- For `And(A;B) == A × B` the formals are free variables A and B. For
  -- binder formals `x.B` we substitute the actual body for that variable.
  let actuals = map btBody bts
      names = map formalName (absFormals abs_)
   in substMany names actuals (absRhs abs_)
  where
    formalName bt = case btVars bt of
      v : _ -> v
      [] -> case btBody bt of
        TVar v -> v
        _ -> dummyVar

-- | Import a theory into a library (does not check proofs).
importTheory :: Theory -> Library -> Either NuprlError Library
importTheory thy lib = do
  let lib' = lib {libTheories = Map.insert (theoryName thy) thy (libTheories lib)}
  Right (foldl add lib' (theoryObjects thy))
  where
    add l (_, ObjSoft names) = setSoft names l
    add l (n, obj) = insertObject n obj l

--------------------------------------------------------------------------------
-- Built-in core library (logic encodings as named abstractions)
--------------------------------------------------------------------------------

coreLibrary :: Library
coreLibrary =
  foldl
    (\l (n, o) -> insertObject n o l)
    emptyLibrary
    coreObjects

coreObjects :: [(Name, Object)]
coreObjects =
  [ comment "Core" "Built-in computational type theory primitives and logic encodings."
  , abs0 "True" TUnit True
  , abs0 "False" TVoid True
  , abs1 "Not" (Var "A") (TNot (TVar (Var "A"))) True
  , abs2 "And" (Var "A") (Var "B") (TAnd (TVar (Var "A")) (TVar (Var "B"))) True
  , abs2 "Or" (Var "A") (Var "B") (TOr (TVar (Var "A")) (TVar (Var "B"))) True
  , abs2 "Implies" (Var "A") (Var "B") (TImplies (TVar (Var "A")) (TVar (Var "B"))) True
  , abs2 "Iff" (Var "A") (Var "B") (TIff (TVar (Var "A")) (TVar (Var "B"))) True
  ]
  where
    comment n t = (n, ObjComment t)
    abs0 n rhs soft =
      ( n
      , ObjAbs
          Abstraction
            { absOpId = OpId n
            , absFormals = []
            , absRhs = rhs
            , absSoft = soft
            }
      )
    abs1 n x rhs soft =
      ( n
      , ObjAbs
          Abstraction
            { absOpId = OpId n
            , absFormals = [bterm0 (TVar x)]
            , absRhs = rhs
            , absSoft = soft
            }
      )
    abs2 n x y rhs soft =
      ( n
      , ObjAbs
          Abstraction
            { absOpId = OpId n
            , absFormals = [bterm0 (TVar x), bterm0 (TVar y)]
            , absRhs = rhs
            , absSoft = soft
            }
      )

--------------------------------------------------------------------------------
-- Display
--------------------------------------------------------------------------------

prettyLibrary :: Library -> Text
prettyLibrary lib =
  T.unlines
    [ T.singleton (statusChar st)
        <> T.singleton (objectKind obj)
        <> " "
        <> n
        <> "  "
        <> summary obj
    | n <- libOrder lib
    , Just obj <- [lookupObject n lib]
    , let st = objectStatus obj
    ]

objectStatus :: Object -> Status
objectStatus = \case
  ObjTheorem th -> thmStatus th
  ObjAbs _ -> StatusComplete
  ObjComment _ -> StatusComplete
  ObjSoft _ -> StatusComplete

summary :: Object -> Text
summary = \case
  ObjTheorem th -> renderTerm (thmGoal th)
  ObjAbs a -> opIdText (absOpId a) <> " == " <> renderTerm (absRhs a)
  ObjComment t -> t
  ObjSoft ns -> "soft " <> T.intercalate ", " ns
