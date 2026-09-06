-- | Capture-avoiding substitution, free variables, and α-equivalence.
--
-- Binding is named (as in NuPRL) rather than nameless. Substitution freshenes
-- binders whenever a captured variable would otherwise appear free in a
-- replacement.
module Nuprl.Subst
  ( -- * Free variables
    freeVars
  , freeVarList
  , occursFree
    -- * Fresh names
  , freshVar
  , freshVars
    -- * Substitution
  , Subst
  , emptySubst
  , singletonSubst
  , subst
  , subst1
  , substMany
  , instantiate
  , instantiate1
    -- * α-equivalence
  , alphaEq
  , alphaEqBound
    -- * Matching
  , matchTerm
  , matchOpen
    -- * Renaming
  , renameVar
  , abstractTerm
  ) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T

import Nuprl.Term

-- | A simultaneous substitution of terms for free variables.
type Subst = Map Var Term

emptySubst :: Subst
emptySubst = Map.empty

singletonSubst :: Var -> Term -> Subst
singletonSubst = Map.singleton

--------------------------------------------------------------------------------
-- Free variables
--------------------------------------------------------------------------------

-- | Free variables of a term.
freeVars :: Term -> Set Var
freeVars = go Set.empty
  where
    go bound (TVar v)
      | v `Set.member` bound || isDummyVar v = Set.empty
      | otherwise = Set.singleton v
    go bound (TOp _ bts) = Set.unions (map (goB bound) bts)
    goB bound (BoundTerm vs t) = go (bound `Set.union` Set.fromList vs) t

freeVarList :: Term -> [Var]
freeVarList = Set.toList . freeVars

occursFree :: Var -> Term -> Bool
occursFree v t = v `Set.member` freeVars t

--------------------------------------------------------------------------------
-- Fresh names
--------------------------------------------------------------------------------

-- | Produce a variable that does not occur in the given set, starting from a
-- suggested name.
freshVar :: Set Var -> Var -> Var
freshVar used v
  | isDummyVar v = freshVar used (Var "x")
  | v `Set.notMember` used = v
  | otherwise = go (1 :: Int)
  where
    base = stripDigits (varText v)
    go n =
      let cand = Var (base <> T.pack (show n))
       in if cand `Set.member` used then go (n + 1) else cand

stripDigits :: Text -> Text
stripDigits = T.dropWhileEnd (\c -> c >= '0' && c <= '9')

-- | Fresh sequence of variables, each distinct from 'used' and from each other.
freshVars :: Set Var -> [Var] -> [Var]
freshVars used = snd . foldl step (used, [])
  where
    step (u, acc) v =
      let v' = freshVar u v
       in (Set.insert v' u, acc ++ [v'])

--------------------------------------------------------------------------------
-- Substitution
--------------------------------------------------------------------------------

-- | Capture-avoiding simultaneous substitution.
subst :: Subst -> Term -> Term
subst s t
  | Map.null s = t
  | otherwise = go s t
  where
    go s' (TVar v) = Map.findWithDefault (TVar v) v s'
    go s' (TOp op bts) = TOp op (map (goB s') bts)

    goB s' (BoundTerm vs body) =
      let -- Drop substitutions for the bound variables.
          sUnbound = foldr Map.delete s' vs
          -- Variables that must stay free (appear in replacements).
          avoid = Set.unions (freeVars body : map freeVars (Map.elems sUnbound))
          vs' = freshVars avoid vs
          renaming =
            Map.fromList
              [ (old, TVar new)
              | (old, new) <- zip vs vs'
              , old /= new
              ]
          s'' = sUnbound `Map.union` renaming
       in BoundTerm vs' (go s'' body)

-- | Substitute a single variable.
subst1 :: Var -> Term -> Term -> Term
subst1 x s = subst (Map.singleton x s)

-- | Substitute a list of variables (zipped with terms). Extra names\/terms
-- are ignored.
substMany :: [Var] -> [Term] -> Term -> Term
substMany vs ts = subst (Map.fromList (zip vs ts))

-- | Instantiate a bound term by substituting the given arguments for its
-- binders. If there are fewer arguments than binders, remaining binders are
-- kept. Extra arguments are ignored.
instantiate :: BoundTerm -> [Term] -> Term
instantiate (BoundTerm vs body) args = substMany vs args body

instantiate1 :: BoundTerm -> Term -> Term
instantiate1 bt a = instantiate bt [a]

--------------------------------------------------------------------------------
-- α-equivalence
--------------------------------------------------------------------------------

-- | α-equivalence of terms. Bound names may differ; free names must agree.
alphaEq :: Term -> Term -> Bool
alphaEq = go []
  where
    go env (TVar x) (TVar y) = matchVar env x y
    go env (TOp op1 bts1) (TOp op2 bts2) =
      op1 == op2
        && length bts1 == length bts2
        && and (zipWith (goB env) bts1 bts2)
    go _ _ _ = False

    goB env (BoundTerm xs t) (BoundTerm ys u) =
      length xs == length ys && go (zip xs ys ++ env) t u

    matchVar env x y =
      case (lookup x env, lookupY y env) of
        (Just y', _) -> y == y'
        (Nothing, Just _) -> False
        (Nothing, Nothing) -> x == y

    lookupY y = lookup y . map swap
    swap (a, b) = (b, a)

alphaEqBound :: BoundTerm -> BoundTerm -> Bool
alphaEqBound (BoundTerm xs t) (BoundTerm ys u) =
  length xs == length ys && alphaEq (renameMany xs ys t) u
  where
    renameMany vs ws = subst (Map.fromList (zip vs (map TVar ws)))

--------------------------------------------------------------------------------
-- Matching
--------------------------------------------------------------------------------

-- | Match a pattern against a term, returning a substitution for the pattern
-- variables in 'pvars'. Operators and binders must agree structurally.
-- Bound pattern variables are not matchable (they must correspond exactly
-- after renaming).
matchTerm :: Set Var -> Term -> Term -> Maybe Subst
matchTerm pvars = matchOpen pvars emptySubst

-- | Matching with an accumulating substitution.
matchOpen :: Set Var -> Subst -> Term -> Term -> Maybe Subst
matchOpen pvars = go []
  where
    go env s (TVar x) t
      | x `Set.member` pvars && not (bound env x) =
          case Map.lookup x s of
            Nothing ->
              -- Reject capture: t must not mention binders currently in scope
              -- in the pattern (those names are not free in the enclosing term).
              if any (`occursFree` t) (map fst env)
                then Nothing
                else Just (Map.insert x t s)
            Just t' -> if alphaEq t t' then Just s else Nothing
      | otherwise =
          case t of
            TVar y | matchVar env x y -> Just s
            _ -> Nothing
    go env s (TOp op1 bts1) (TOp op2 bts2)
      | op1 == op2 && length bts1 == length bts2 =
          foldl step (Just s) (zip bts1 bts2)
      | otherwise = Nothing
      where
        step Nothing _ = Nothing
        step (Just s') (b1, b2) = goB env s' b1 b2
    go _ _ _ _ = Nothing

    goB env s (BoundTerm xs t) (BoundTerm ys u)
      | length xs == length ys = go (zip xs ys ++ env) s t u
      | otherwise = Nothing

    bound env x = any ((== x) . fst) env

    matchVar env x y =
      case (lookup x env, lookup y (map (\(a, b) -> (b, a)) env)) of
        (Just y', _) -> y == y'
        (Nothing, Just _) -> False
        (Nothing, Nothing) -> x == y

--------------------------------------------------------------------------------
-- Renaming
--------------------------------------------------------------------------------

-- | Rename a single free variable.
renameVar :: Var -> Var -> Term -> Term
renameVar old new = subst1 old (TVar new)

-- | Bind a list of free variables, producing a 'BoundTerm'.
abstractTerm :: [Var] -> Term -> BoundTerm
abstractTerm = BoundTerm
