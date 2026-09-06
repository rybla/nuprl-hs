-- | Sequents of NuPRL computational type theory.
--
-- A sequent is
--
-- > H1, ..., Hn ⊢ C
--
-- where each hypothesis is a (possibly hidden) typed declaration @x : T@.
-- Hidden hypotheses — displayed in brackets — cannot appear in extracts; they
-- arise from squash elimination and similar rules (NuPRL §9.12).
--
-- All hypotheses declare distinct variables. A declaration whose variable
-- begins with @\'%\'@ is /invisible/ and is omitted from pretty-printing.
module Nuprl.Sequent
  ( Hypothesis (..)
  , hypVar
  , hypType
  , hypHidden
  , visibleHyp
  , hiddenHyp
  , Sequent (..)
  , emptySequent
  , conclusion
  , hypotheses
  , addHyp
  , addHyps
  , lookupHyp
  , lookupHypIndex
  , nthHyp
  , hypCount
  , declaredVars
  , sequentFreeVars
  , isClosedSequent
  , hideHyp
  , hideAllHyps
  , prettySequent
  , prettyHypothesis
  , ClauseIndex
  , conclusionIndex
  , clauseType
  ) where

import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Prettyprinter

import Nuprl.Pretty (docToText, prettyTerm)
import Nuprl.Subst
import Nuprl.Term

-- | A single hypothesis: a typed declaration, possibly hidden.
data Hypothesis = Hypothesis
  { hVar :: Var
  , hType :: Term
  , hHidden :: Bool
  }
  deriving stock (Eq, Show)

hypVar :: Hypothesis -> Var
hypVar = hVar

hypType :: Hypothesis -> Term
hypType = hType

hypHidden :: Hypothesis -> Bool
hypHidden = hHidden

visibleHyp :: Var -> Term -> Hypothesis
visibleHyp x ty = Hypothesis x ty False

hiddenHyp :: Var -> Term -> Hypothesis
hiddenHyp x ty = Hypothesis x ty True

-- | A sequent @H ⊢ C@.
data Sequent = Sequent
  { seqHyps :: [Hypothesis]
  , seqConcl :: Term
  }
  deriving stock (Eq, Show)

emptySequent :: Term -> Sequent
emptySequent = Sequent []

conclusion :: Sequent -> Term
conclusion = seqConcl

hypotheses :: Sequent -> [Hypothesis]
hypotheses = seqHyps

-- | Append a hypothesis, freshening its variable if needed.
addHyp :: Hypothesis -> Sequent -> Sequent
addHyp h sq =
  let used = declaredVars sq
      x' = freshVar used (hVar h)
      h' = h {hVar = x'}
      concl' =
        if x' == hVar h
          then seqConcl sq
          else subst1 (hVar h) (TVar x') (seqConcl sq)
   in sq {seqHyps = seqHyps sq ++ [h'], seqConcl = concl'}

addHyps :: [Hypothesis] -> Sequent -> Sequent
addHyps hs sq = foldl (flip addHyp) sq hs

-- | 1-based index, in the NuPRL convention.
lookupHyp :: Int -> Sequent -> Maybe Hypothesis
lookupHyp i sq
  | i >= 1 && i <= length (seqHyps sq) = Just (seqHyps sq !! (i - 1))
  | otherwise = Nothing

-- | Find the (1-based) index of a hypothesis by name.
lookupHypIndex :: Var -> Sequent -> Maybe Int
lookupHypIndex x sq =
  case [i | (i, h) <- zip [1 ..] (seqHyps sq), hVar h == x] of
    i : _ -> Just i
    [] -> Nothing

nthHyp :: Int -> Sequent -> Maybe Hypothesis
nthHyp = lookupHyp

hypCount :: Sequent -> Int
hypCount = length . seqHyps

declaredVars :: Sequent -> Set Var
declaredVars sq = Set.fromList (map hVar (seqHyps sq))

sequentFreeVars :: Sequent -> Set Var
sequentFreeVars sq =
  let hypFVs =
        Set.unions
          [ freeVars (hType h) `Set.difference` Set.fromList (map hVar (take (i - 1) (seqHyps sq)))
          | (i, h) <- zip [1 ..] (seqHyps sq)
          ]
      bound = declaredVars sq
   in hypFVs `Set.union` (freeVars (seqConcl sq) `Set.difference` bound)

-- | A sequent is closed when every free variable of a clause is bound by an
-- earlier declaration.
isClosedSequent :: Sequent -> Bool
isClosedSequent sq = Set.null (sequentFreeVars sq)

hideHyp :: Int -> Sequent -> Sequent
hideHyp i sq =
  sq
    { seqHyps =
        [ if j == i then h {hHidden = True} else h
        | (j, h) <- zip [1 ..] (seqHyps sq)
        ]
    }

hideAllHyps :: Sequent -> Sequent
hideAllHyps sq = sq {seqHyps = [h {hHidden = True} | h <- seqHyps sq]}

--------------------------------------------------------------------------------
-- Clause indexing (NuPRL: 0 = conclusion, i > 0 = hypothesis i)
--------------------------------------------------------------------------------

-- | A clause index: @0@ is the conclusion, @i > 0@ is hypothesis @i@.
type ClauseIndex = Int

conclusionIndex :: ClauseIndex
conclusionIndex = 0

-- | Type of a clause. For the conclusion this is the conclusion itself.
clauseType :: Sequent -> ClauseIndex -> Maybe Term
clauseType sq 0 = Just (seqConcl sq)
clauseType sq i = hType <$> lookupHyp i sq

--------------------------------------------------------------------------------
-- Pretty-printing
--------------------------------------------------------------------------------

prettyHypothesis :: Int -> Hypothesis -> Doc ann
prettyHypothesis i h =
  pretty i <> "."
    <+> hide
      ( if isHiddenVar (hVar h) || isDummyVar (hVar h)
          then prettyTerm (hType h)
          else pretty (varText (hVar h)) <+> ":" <+> prettyTerm (hType h)
      )
  where
    hide d = if hHidden h then brackets d else d

prettySequentDoc :: Sequent -> Doc ann
prettySequentDoc sq =
  vsep $
    [prettyHypothesis i h | (i, h) <- zip [1 ..] (seqHyps sq)]
      ++ ["⊢" <+> prettyTerm (seqConcl sq)]

prettySequent :: Sequent -> Text
prettySequent = docToText . prettySequentDoc
