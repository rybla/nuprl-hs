-- | A modern Haskell implementation of the NuPRL proof development system.
--
-- nuprl-hs implements computational type theory (CTT) as a refinement theorem
-- prover. The kernel ('Nuprl.Rule') is a pure function from sequents to
-- subgoals and extracts; tactics ('Nuprl.Tactic') search for kernel
-- derivations; theories ('Nuprl.Library') are text files checked by replaying
-- tactic scripts.
--
-- IO is confined to 'Nuprl.CLI' and 'Nuprl.REPL'. Import the specialised
-- modules ('Nuprl.Term', 'Nuprl.Tactic', …) for the full API.
module Nuprl
  ( -- * Terms
    Term (..)
  , Var (..)
  , LevelExp (..)
  , renderTerm
  , parseTerm
  , alphaEq
  , subst1
  , whnf
  , normalize
    -- * Sequents and proofs
  , Sequent (..)
  , Proof (..)
  , TacticExpr (..)
  , prove
  , proveExpr
    -- * Library
  , Library
  , Theory (..)
  , emptyLibrary
  , coreLibrary
  , checkTheory
    -- * Errors
  , NuprlError (..)
  , prettyError
  ) where

import Nuprl.Check (checkTheory, prove, proveExpr)
import Nuprl.Compute (normalize, whnf)
import Nuprl.Error (NuprlError (..), prettyError)
import Nuprl.Library (Library, Theory (..), coreLibrary, emptyLibrary)
import Nuprl.Parse (parseTerm)
import Nuprl.Pretty (renderTerm)
import Nuprl.Proof (Proof (..))
import Nuprl.Sequent (Sequent (..))
import Nuprl.Subst (alphaEq, subst1)
import Nuprl.Tactic (TacticExpr (..))
import Nuprl.Term (LevelExp (..), Term (..), Var (..))
