-- | Checking theories: replay tactic scripts against theorem statements.
--
-- Checking is a pure function from a 'Library' and a 'Theory' to an updated
-- library (with statuses and extracts filled in) or a 'NuprlError'.
module Nuprl.Check
  ( checkTheory
  , checkTheorem
  , checkLibrary
  , prove
  , proveExpr
  ) where

import Data.Text qualified as T

import Nuprl.Error
import Nuprl.Library
import Nuprl.Proof
import Nuprl.Sequent
import Nuprl.Tactic
import Nuprl.Term

-- | Start an empty proof of a closed goal.
startProof :: Term -> Proof
startProof goal = Unrefined (emptySequent goal)

-- | Run a tactic expression against a goal, requiring completeness.
proveExpr :: Library -> Term -> TacticExpr -> Either NuprlError (Proof, Term)
proveExpr lib goal script = do
  let env = lemmaEnv lib
      tac = evalTactic script
      p0 = startProof goal
  p <- case applyTactic env tac p0 of
    Left tf -> Left (ErrTactic tf)
    Right p' -> Right p'
  if not (isComplete p)
    then
      Left
        ( ErrCheck $
            "proof is incomplete ("
              <> T.pack (show (openCount p))
              <> " open goal(s))\n"
              <> prettyProof p
        )
    else case extractProof p of
      Left re -> Left (ErrRefine re)
      Right e -> Right (p, e)

-- | Prove a goal with a tactic script, returning the extract.
prove :: Library -> Term -> TacticExpr -> Either NuprlError Term
prove lib goal script = snd <$> proveExpr lib goal script

-- | Check a single theorem object, returning the updated theorem.
checkTheorem :: Library -> Name -> Theorem -> Either NuprlError Theorem
checkTheorem lib name th =
  case proveExpr lib (thmGoal th) (thmScript th) of
    Left err ->
      Left (ErrCheck ("theorem " <> name <> ": " <> prettyError err))
    Right (_, extr) ->
      Right
        th
          { thmStatus = StatusComplete
          , thmExtract = Just extr
          }

-- | Check every theorem in a theory, in order. Abstractions are installed
-- before subsequent theorems so they may be referenced.
checkTheory :: Library -> Theory -> Either NuprlError Library
checkTheory lib0 thy = do
  lib1 <- importTheory thy lib0
  go lib1 (theoryObjects thy)
  where
    go lib [] = Right lib
    go lib ((n, ObjTheorem th) : rest) = do
      th' <- checkTheorem lib n th
      go (insertObject n (ObjTheorem th') lib) rest
    go lib (_ : rest) = go lib rest

-- | Re-check every theorem currently in the library.
checkLibrary :: Library -> Either NuprlError Library
checkLibrary lib = go lib (libraryTheorems lib)
  where
    go l [] = Right l
    go l ((n, th) : rest) = do
      th' <- checkTheorem l n th
      go (insertObject n (ObjTheorem th') l) rest
