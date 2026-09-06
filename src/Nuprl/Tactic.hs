-- | Tactic language for NuPRL.
--
-- A tactic is a (pure) function from a focused proof node to a refined proof.
-- Combinators ('tacThen', 'tacOrElse', 'tacRepeat', …) are the standard LCF
-- ones (NuPRL §9). Primitive tactics wrap the refiner; 'tacAuto' is a
-- bounded proof search that discharges a useful fragment of CTT.
module Nuprl.Tactic
  ( -- * Semantic tactics
    Tactic
  , runTactic
  , applyTactic
    -- * Combinators
  , tacId
  , tacFail
  , tacThen
  , tacThenL
  , tacOrElse
  , tacTry
  , tacRepeat
  , tacProgress
    -- * Primitive tactics
  , tacHyp
  , tacHypAny
  , tacIntro
  , tacElim
  , tacEq
  , tacCompute
  , tacCut
  , tacLemma
  , tacThin
  , tacD
  , tacAssumption
  , tacLeft
  , tacRight
  , tacSplit
  , tacExists
  , tacExact
  , tacUnfold
  , tacReduce
  , tacDecideInt
  , tacCases
    -- * Automation
  , tacAuto
  , tacAutoN
  , tacProveProp
  , tacArith
    -- * Tactic scripts
  , TacticExpr (..)
  , IntroArgExpr (..)
  , evalTactic
  , prettyTacticExpr
  ) where

import Data.Text (Text)
import Data.Text qualified as T

import Nuprl.Compute (whnf)
import Nuprl.Error
import Nuprl.Proof
import Nuprl.Rule
import Nuprl.Sequent
import Nuprl.Term

-- | A tactic acts on the focused node of a proof.
newtype Tactic = Tactic
  { runTactic :: LemmaEnv -> Proof -> Addr -> Either TacticFail Proof
  }

-- | Apply a tactic to the first open goal, or to the root if the proof is a
-- single unrefined node.
applyTactic :: LemmaEnv -> Tactic -> Proof -> Either TacticFail Proof
applyTactic env tac p =
  case openGoals p of
    (addr, _) : _ -> runTactic tac env p addr
    [] -> Left (TacticFail "apply" "no open goals")

failT :: Text -> Text -> Either TacticFail a
failT name reason = Left (TacticFail name reason)

-- | Lift a primitive rule to a tactic on the focused node.
primTac :: Text -> PrimitiveRule -> Tactic
primTac name rule = Tactic $ \env p addr ->
  case refineAt env rule addr p of
    Right p' -> Right p'
    Left (RefineError r reason) -> failT name (r <> ": " <> reason)

--------------------------------------------------------------------------------
-- Combinators
--------------------------------------------------------------------------------

-- | Do nothing.
tacId :: Tactic
tacId = Tactic $ \_ p _ -> Right p

-- | Always fail.
tacFail :: Text -> Tactic
tacFail msg = Tactic $ \_ _ _ -> failT "fail" msg

-- | Sequential composition: run @t2@ on every new open goal produced by @t1@
-- (the classic THEN, which is depth-first on the newly created leaves).
tacThen :: Tactic -> Tactic -> Tactic
tacThen t1 t2 = Tactic $ \env p addr -> do
  p1 <- runTactic t1 env p addr
  -- Apply t2 to each open goal that is under `addr`.
  let new = [a | (a, _) <- openGoals p1, addr `isPrefixAddr` a]
  go env p1 new
  where
    go _ p' [] = Right p'
    go env p' (a : as) = case runTactic t2 env p' a of
      Right p'' -> go env p'' as
      Left err -> Left err

isPrefixAddr :: Addr -> Addr -> Bool
isPrefixAddr (Addr xs) (Addr ys) = xs == take (length xs) ys

-- | Like 'tacThen', but the second argument is a list of tactics, one per
-- subgoal produced by the first tactic. Extra tactics are ignored; missing
-- tactics default to 'tacId'.
tacThenL :: Tactic -> [Tactic] -> Tactic
tacThenL t1 ts = Tactic $ \env p addr -> do
  p1 <- runTactic t1 env p addr
  -- Immediate children of addr that are still open, or their open descendants
  -- if the child was itself refined... THENL is defined on the *immediate*
  -- subgoals of the refined node.
  sub <- case proofAt addr p1 of
    Right (Refined _ _ cs _) -> Right (zip [0 ..] cs)
    Right (Unrefined _) -> failT "THENL" "first tactic produced no subgoals"
    Left (RefineError _ r) -> failT "THENL" r
  let pairings =
        [ (extendAddr addr i, if i < length ts then ts !! i else tacId)
        | (i, _) <- sub
        ]
  go env p1 pairings
  where
    go _ p' [] = Right p'
    go env p' ((a, t) : rest) = do
      -- If the child is already complete, skip.
      case proofAt a p' of
        Right c | isComplete c -> go env p' rest
        _ -> do
          p'' <- runTactic t env p' a
          go env p'' rest

-- | Try @t1@; if it fails, try @t2@ on the original goal.
tacOrElse :: Tactic -> Tactic -> Tactic
tacOrElse t1 t2 = Tactic $ \env p addr ->
  case runTactic t1 env p addr of
    Right p' -> Right p'
    Left _ -> runTactic t2 env p addr

-- | 'tacOrElse' 'tacId'.
tacTry :: Tactic -> Tactic
tacTry t = tacOrElse t tacId

-- | Repeat until failure. Always succeeds (zero iterations is 'tacId').
tacRepeat :: Tactic -> Tactic
tacRepeat t = tacOrElse (tacProgress t `tacThen` tacRepeat t) tacId

-- | Fail unless the tactic actually changes the focused node.
tacProgress :: Tactic -> Tactic
tacProgress t = Tactic $ \env p addr -> do
  p' <- runTactic t env p addr
  case (proofAt addr p, proofAt addr p') of
    (Right (Unrefined _), Right (Unrefined _)) ->
      failT "progress" "tactic made no progress"
    _ -> Right p'

infixr 1 `tacThen`
infixr 0 `tacOrElse`

--------------------------------------------------------------------------------
-- Primitive tactics
--------------------------------------------------------------------------------

tacHyp :: Int -> Tactic
tacHyp i = primTac "hyp" (RuleHyp i)

-- | Try every hypothesis, left to right.
tacHypAny :: Tactic
tacHypAny = Tactic $ \env p addr ->
  case proofAt addr p of
    Left (RefineError _ r) -> failT "hyp" r
    Right sub ->
      let n = hypCount (proofGoal sub)
          tries = map tacHyp [n, n - 1 .. 1]
       in runTactic (foldr tacOrElse (tacFail "no hypothesis applies") tries) env p addr

tacIntro :: IntroArg -> Tactic
tacIntro arg = primTac "intro" (RuleIntro arg)

tacElim :: Int -> ElimArg -> Tactic
tacElim i arg = primTac "elim" (RuleElim i arg)

tacEq :: Tactic
tacEq = primTac "eq" RuleEq

tacCompute :: Tactic
tacCompute = primTac "compute" RuleCompute

tacCut :: Term -> Var -> Tactic
tacCut ty x = primTac "cut" (RuleCut ty x)

tacLemma :: Name -> [Term] -> Tactic
tacLemma n args = primTac "lemma" (RuleLemma n args)

tacThin :: Int -> Tactic
tacThin i = primTac "thin" (RuleThin i)

tacLeft :: Tactic
tacLeft = tacIntro IntroLeft

tacRight :: Tactic
tacRight = tacIntro IntroRight

tacSplit :: Tactic
tacSplit = tacIntro (IntroInfer Nothing)

tacExists :: Term -> Tactic
tacExists t = tacIntro (IntroWitness t)

tacAssumption :: Tactic
tacAssumption = tacHypAny

tacExact :: Term -> Tactic
tacExact t = tacCut t (Var "h") `tacThen` tacIntro (IntroWitness t) `tacThen` tacHypAny

-- | Case analysis on integer equality.
tacDecideInt :: Term -> Term -> Tactic
tacDecideInt a b = primTac "decide" (RuleDecideInt a b)

-- | Case analysis on a term of union type.
tacCases :: Term -> Tactic
tacCases t = primTac "decide" (RuleCases t)

-- | Unfold a soft encoding (or compute) at the conclusion.
tacUnfold :: Tactic
tacUnfold = tacCompute `tacOrElse` tacId

-- | Repeated weak-head computation of the conclusion. Sound: each step is
-- a primitive 'RuleCompute'.
tacReduce :: Tactic
tacReduce = tacRepeat tacCompute

-- | Decompose clause @i@ (0 = conclusion), the NuPRL @D@ tactic.
tacD :: ClauseIndex -> Tactic
tacD 0 = Tactic $ \env p addr ->
  runTactic
    ( tacEq
        `tacOrElse` tacIntro (IntroInfer Nothing)
        `tacOrElse` tacLeft
        `tacOrElse` tacRight
        `tacOrElse` tacCompute
    )
    env
    p
    addr
tacD i = Tactic $ \env p addr ->
  runTactic (tacElim i ElimBare `tacOrElse` tacHyp i) env p addr

--------------------------------------------------------------------------------
-- Automation
--------------------------------------------------------------------------------

-- | Default automation depth.
tacAuto :: Tactic
tacAuto = tacAutoN 6

-- | Bounded proof search.
tacAutoN :: Int -> Tactic
tacAutoN n
  | n <= 0 = tacHypAny `tacOrElse` tacEq `tacOrElse` trivialIntro
  | otherwise =
      tacHypAny
        `tacOrElse` (tacEq `tacThen` tacAutoN (n - 1))
        `tacOrElse` (trivialIntro `tacThen` tacAutoN (n - 1))
        `tacOrElse` (tacIntro (IntroInfer Nothing) `tacThen` tacAutoN (n - 1))
        `tacOrElse` elimFirst `tacThenMaybe` n
        `tacOrElse` tacCompute `tacThen` tacAutoN (n - 1)

trivialIntro :: Tactic
trivialIntro = Tactic $ \env p addr ->
  case proofAt addr p of
    Right sub ->
      case headForm (seqConcl (proofGoal sub)) of
        TUnit -> runTactic (tacIntro (IntroInfer Nothing)) env p addr
        TTrue -> runTactic (tacIntro (IntroInfer Nothing)) env p addr
        TEqual {} -> runTactic tacEq env p addr
        _ -> failT "auto" "not a trivial introduction"
    Left (RefineError _ r) -> failT "auto" r

-- | Eliminate the first hypothesis that can be eliminated without a witness.
elimFirst :: Tactic
elimFirst = Tactic $ \env p addr ->
  case proofAt addr p of
    Left (RefineError _ r) -> failT "auto" r
    Right sub ->
      let n = hypCount (proofGoal sub)
          tries = [tacElim i ElimBare | i <- [1 .. n]]
       in runTactic (foldr tacOrElse (tacFail "no elim") tries) env p addr

-- | THEN that still fails if the first tactic fails; used to sequence elim
-- with a shallower auto so we do not explode the search.
tacThenMaybe :: Tactic -> Int -> Tactic
tacThenMaybe t n = t `tacThen` tacAutoN (n - 1)

-- | Propositional tableau (a simplified ProveProp).
tacProveProp :: Tactic
tacProveProp = tacAutoN 8

-- | Closed integer facts, discharged by computation + reflexivity.
tacArith :: Tactic
tacArith = Tactic $ \env p addr ->
  case proofAt addr p of
    Left (RefineError _ r) -> failT "arith" r
    Right sub ->
      let c = headForm (seqConcl (proofGoal sub))
       in case c of
            TEqual TInt a b ->
              case (whnf a, whnf b) of
                (TNat n, TNat m)
                  | n == m -> runTactic tacEq env p addr
                _ -> failT "arith" "not a closed integer equality"
            TMember a TInt ->
              case whnf a of
                TNat _ -> runTactic tacEq env p addr
                _ -> failT "arith" "not a closed integer"
            _ -> failT "arith" "not an arithmetic goal"

--------------------------------------------------------------------------------
-- Tactic scripts (surface language)
--------------------------------------------------------------------------------

-- | Surface syntax of tactic scripts, as stored in theory files and entered
-- at the REPL. Evaluation is the pure function 'evalTactic'.
data TacticExpr
  = TxId
  | TxFail
  | TxIntro IntroArgExpr
  | TxElim Int (Maybe Term)
  | TxHyp (Maybe Int)
  | TxAuto
  | TxAutoN Int
  | TxD (Maybe Int)
  | TxEq
  | TxCompute
  | TxReduce
  | TxUnfold
  | TxArith
  | TxProveProp
  | TxLeft
  | TxRight
  | TxSplit
  | TxExists Term
  | TxAssumption
  | TxCut Term (Maybe Var)
  | TxLemma Name [Term]
  | TxThin Int
  | TxDecideInt Term Term
  | TxCases Term
  | TxThen TacticExpr TacticExpr
  | TxThenL TacticExpr [TacticExpr]
  | TxOrElse TacticExpr TacticExpr
  | TxRepeat TacticExpr
  | TxTry TacticExpr
  | TxSeq [TacticExpr]
  deriving stock (Eq, Show)

data IntroArgExpr
  = IxInfer (Maybe Var)
  | IxLeft
  | IxRight
  | IxWitness Term
  deriving stock (Eq, Show)

-- | Interpret a tactic script.
evalTactic :: TacticExpr -> Tactic
evalTactic = \case
  TxId -> tacId
  TxFail -> tacFail "fail"
  TxIntro (IxInfer mx) -> tacIntro (IntroInfer mx)
  TxIntro IxLeft -> tacIntro IntroLeft
  TxIntro IxRight -> tacIntro IntroRight
  TxIntro (IxWitness t) -> tacIntro (IntroWitness t)
  TxElim i Nothing -> tacElim i ElimBare
  TxElim i (Just t) -> tacElim i (ElimWitness t)
  TxHyp Nothing -> tacHypAny
  TxHyp (Just i) -> tacHyp i
  TxAuto -> tacAuto
  TxAutoN n -> tacAutoN n
  TxD Nothing -> tacD 0
  TxD (Just i) -> tacD i
  TxEq -> tacEq
  TxCompute -> tacCompute
  TxReduce -> tacReduce
  TxUnfold -> tacUnfold
  TxArith -> tacArith
  TxProveProp -> tacProveProp
  TxLeft -> tacLeft
  TxRight -> tacRight
  TxSplit -> tacSplit
  TxExists t -> tacExists t
  TxAssumption -> tacAssumption
  TxCut ty mx -> tacCut ty (maybe (Var "h") id mx)
  TxLemma n args -> tacLemma n args
  TxThin i -> tacThin i
  TxDecideInt a b -> tacDecideInt a b
  TxCases t -> tacCases t
  TxThen a b -> evalTactic a `tacThen` evalTactic b
  TxThenL a bs -> tacThenL (evalTactic a) (map evalTactic bs)
  TxOrElse a b -> evalTactic a `tacOrElse` evalTactic b
  TxRepeat a -> tacRepeat (evalTactic a)
  TxTry a -> tacTry (evalTactic a)
  TxSeq [] -> tacId
  TxSeq [x] -> evalTactic x
  TxSeq (x : xs) -> evalTactic x `tacThen` evalTactic (TxSeq xs)

prettyTacticExpr :: TacticExpr -> Text
prettyTacticExpr = \case
  TxId -> "idtac"
  TxFail -> "fail"
  TxIntro (IxInfer Nothing) -> "intro"
  TxIntro (IxInfer (Just x)) -> "intro " <> varText x
  TxIntro IxLeft -> "intro left"
  TxIntro IxRight -> "intro right"
  TxIntro (IxWitness _) -> "intro with …"
  TxElim i Nothing -> "elim " <> tshow i
  TxElim i (Just _) -> "elim " <> tshow i <> " with …"
  TxHyp Nothing -> "hyp"
  TxHyp (Just i) -> "hyp " <> tshow i
  TxAuto -> "auto"
  TxAutoN n -> "auto " <> tshow n
  TxD Nothing -> "D"
  TxD (Just i) -> "D " <> tshow i
  TxEq -> "eq"
  TxCompute -> "compute"
  TxReduce -> "reduce"
  TxUnfold -> "unfold"
  TxArith -> "arith"
  TxProveProp -> "prove_prop"
  TxLeft -> "left"
  TxRight -> "right"
  TxSplit -> "split"
  TxExists _ -> "exists …"
  TxAssumption -> "assumption"
  TxCut {} -> "cut …"
  TxLemma n _ -> "lemma " <> n
  TxThin i -> "thin " <> tshow i
  TxDecideInt {} -> "decide … = …"
  TxCases {} -> "decide …"
  TxThen a b -> prettyTacticExpr a <> " THEN " <> prettyTacticExpr b
  TxThenL a _ -> prettyTacticExpr a <> " THENL …"
  TxOrElse a b -> prettyTacticExpr a <> " ORELSE " <> prettyTacticExpr b
  TxRepeat a -> "REPEAT " <> prettyTacticExpr a
  TxTry a -> "TRY " <> prettyTacticExpr a
  TxSeq ts -> T.intercalate "; " (map prettyTacticExpr ts)

tshow :: (Show a) => a -> Text
tshow = T.pack . show
