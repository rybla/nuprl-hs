-- | Refinement proof trees.
--
-- A proof is either an unrefined sequent (an open goal) or a sequent refined
-- by a primitive rule together with proofs of the generated subgoals. The
-- extract of a complete proof is recovered by applying each node's extract
-- combinator to the extracts of its children (NuPRL §7.3).
module Nuprl.Proof
  ( Proof (..)
  , proofGoal
  , isComplete
  , isGood
  , openGoals
  , openCount
  , Addr (..)
  , rootAddr
  , extendAddr
  , addrChildren
  , proofAt
  , mapAt
  , refineAt
  , extractProof
  , prettyProof
  , prettyProofFocused
  ) where

import Data.Text (Text)
import Data.Text qualified as T
import Prettyprinter

import Nuprl.Error
import Nuprl.Pretty (docToText)
import Nuprl.Rule
import Nuprl.Sequent
import Nuprl.Term

-- | A refinement proof tree.
data Proof
  = Unrefined Sequent
  | Refined Sequent Text [Proof] ([Term] -> Term)

instance Show Proof where
  show = T.unpack . prettyProof

-- | Goal sequent at the root of a proof.
proofGoal :: Proof -> Sequent
proofGoal (Unrefined s) = s
proofGoal (Refined s _ _ _) = s

-- | A proof is complete when it is a tree of refined nodes with no unrefined
-- leaves.
isComplete :: Proof -> Bool
isComplete (Unrefined _) = False
isComplete (Refined _ _ cs _) = all isComplete cs

-- | A proof is "good" when every sequent is closed. Completeness is separate.
isGood :: Proof -> Bool
isGood (Unrefined s) = isClosedSequent s
isGood (Refined s _ cs _) = isClosedSequent s && all isGood cs

-- | Addresses of unrefined leaves, in left-to-right order.
openGoals :: Proof -> [(Addr, Sequent)]
openGoals = go rootAddr
  where
    go addr (Unrefined s) = [(addr, s)]
    go addr (Refined _ _ cs _) =
      concat [go (extendAddr addr i) p | (i, p) <- zip [0 ..] cs]

openCount :: Proof -> Int
openCount = length . openGoals

-- | Path from the root. Each integer selects a child.
newtype Addr = Addr [Int]
  deriving stock (Eq, Ord, Show)

rootAddr :: Addr
rootAddr = Addr []

extendAddr :: Addr -> Int -> Addr
extendAddr (Addr xs) i = Addr (xs ++ [i])

addrChildren :: Addr -> Int -> [Addr]
addrChildren addr n = [extendAddr addr i | i <- [0 .. n - 1]]

-- | Subproof at an address.
proofAt :: Addr -> Proof -> Either RefineError Proof
proofAt (Addr []) p = Right p
proofAt (Addr (i : is)) (Refined _ _ cs _)
  | i >= 0 && i < length cs = proofAt (Addr is) (cs !! i)
proofAt _ _ = Left (RefineError "proofAt" "invalid proof address")

-- | Replace the subproof at an address.
mapAt :: Addr -> (Proof -> Either RefineError Proof) -> Proof -> Either RefineError Proof
mapAt (Addr []) f p = f p
mapAt (Addr (i : is)) f (Refined g n cs e)
  | i >= 0 && i < length cs = do
      cs' <- replace i (\c -> mapAt (Addr is) f c) cs
      Right (Refined g n cs' e)
mapAt _ _ _ = Left (RefineError "mapAt" "invalid proof address")

replace :: Int -> (a -> Either e a) -> [a] -> Either e [a]
replace i f xs =
  case splitAt i xs of
    (pre, x : post) -> do
      x' <- f x
      Right (pre ++ x' : post)
    _ -> error "replace: index out of range"

-- | Refine the unrefined node at 'Addr' with a primitive rule.
refineAt :: LemmaEnv -> PrimitiveRule -> Addr -> Proof -> Either RefineError Proof
refineAt env rule addr = mapAt addr $ \case
  Unrefined sq -> do
    rr <- applyRule env rule sq
    let children = map (Unrefined . lgSequent) (rrSubgoals rr)
    Right (Refined sq (rrName rr) children (rrExtract rr))
  Refined {} ->
    Left (RefineError (rrNameDummy rule) "node is already refined")

rrNameDummy :: PrimitiveRule -> Text
rrNameDummy = \case
  RuleHyp i -> "hyp " <> tshow i
  RuleIntro _ -> "intro"
  RuleElim i _ -> "elim " <> tshow i
  RuleEq -> "eq"
  RuleCompute -> "compute"
  RuleCut {} -> "cut"
  RuleLemma n _ -> "lemma " <> n
  RuleThin i -> "thin " <> tshow i
  RuleCumulativity _ -> "cumulativity"

-- | Extract the computational content of a complete proof.
extractProof :: Proof -> Either RefineError Term
extractProof (Unrefined _) =
  Left (RefineError "extract" "proof is incomplete")
extractProof (Refined _ _ cs e) = do
  es <- traverse extractProof cs
  Right (e es)

--------------------------------------------------------------------------------
-- Pretty-printing
--------------------------------------------------------------------------------

prettyProof :: Proof -> Text
prettyProof = prettyProofFocused Nothing

prettyProofFocused :: Maybe Addr -> Proof -> Text
prettyProofFocused mfocus = docToText . go rootAddr 0
  where
    go addr padAmt p =
      let pad = pretty (replicate padAmt ' ' :: String)
          mark =
            if Just addr == mfocus
              then pretty ("▶ " :: Text)
              else pretty ("  " :: Text)
          goalDoc sq = vsep (map (\l -> pad <> pretty l) (T.lines (prettySequent sq)))
       in case p of
            Unrefined sq ->
              mark <> pretty ("goal " :: Text) <> pretty (showAddr addr)
                <> hardline
                <> goalDoc sq
            Refined sq name cs _ ->
              let kids =
                    vsep
                      [ go (extendAddr addr i) (padAmt + 2) c
                      | (i, c) <- zip [0 ..] cs
                      ]
               in mark <> goalDoc sq
                    <> hardline
                    <> pad
                    <> pretty ("BY " :: Text)
                    <> pretty name
                    <> if null cs
                      then mempty
                      else hardline <> kids

showAddr :: Addr -> Text
showAddr (Addr xs) = T.intercalate "." (map tshow xs)

tshow :: (Show a) => a -> Text
tshow = T.pack . show
