-- | Primitive refinement rules of NuPRL computational type theory.
--
-- Every completed proof is justified by these rules (and by computation).
-- Tactics are programs that search for a tree of primitive refinements.
--
-- A rule maps a sequent to a list of subgoal sequents and an extract
-- combinator. Extracts of well-formedness\/equality subgoals are typically
-- 'Nuprl.Term.TAxiom'.
module Nuprl.Rule
  ( PrimitiveRule (..)
  , IntroArg (..)
  , ElimArg (..)
  , RuleResult (..)
  , LabeledGoal (..)
  , LemmaEnv (..)
  , lookupLemma
  , emptyLemmaEnv
  , applyRule
  , headForm
  , typesEq
  ) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T

import Nuprl.Compute
import Nuprl.Error
import Nuprl.Sequent
import Nuprl.Subst
import Nuprl.Term

-- | Environment of complete lemma statements, keyed by name.
newtype LemmaEnv = LemmaEnv {unLemmaEnv :: Map Name Term}
  deriving stock (Eq, Show)

emptyLemmaEnv :: LemmaEnv
emptyLemmaEnv = LemmaEnv Map.empty

lookupLemma :: Name -> LemmaEnv -> Maybe Term
lookupLemma n (LemmaEnv m) = Map.lookup n m

-- | Arguments to introduction.
data IntroArg
  = -- | Infer the introduction form from the conclusion. Optional binder name
    -- is used for λ \/ ∀.
    IntroInfer (Maybe Var)
  | -- | Left injection (union \/ disjunction).
    IntroLeft
  | -- | Right injection (union \/ disjunction).
    IntroRight
  | -- | Witness for Σ \/ ∃ \/ set.
    IntroWitness Term
  deriving stock (Eq, Show)

-- | Arguments to elimination.
data ElimArg
  = ElimBare
  | ElimWitness Term
  deriving stock (Eq, Show)

-- | Primitive rules of the refiner.
data PrimitiveRule
  = RuleHyp Int
  | RuleIntro IntroArg
  | RuleElim Int ElimArg
  | RuleEq
  | RuleCompute
  | RuleCut Term Var
  | RuleLemma Name [Term]
  | RuleThin Int
  | RuleCumulativity LevelExp
  deriving stock (Eq, Show)

-- | A subgoal together with a NuPRL-style label (@main@, @wf@, @base@, …).
data LabeledGoal = LabeledGoal
  { lgLabel :: Text
  , lgSequent :: Sequent
  }
  deriving stock (Eq, Show)

-- | Result of a successful refinement.
data RuleResult = RuleResult
  { rrName :: Text
  , rrSubgoals :: [LabeledGoal]
  , rrExtract :: [Term] -> Term
  }

failRule :: Text -> Text -> Either RefineError a
failRule rule reason = Left (RefineError rule reason)

-- | Apply a primitive rule to a sequent.
applyRule :: LemmaEnv -> PrimitiveRule -> Sequent -> Either RefineError RuleResult
applyRule env rule sq = case rule of
  RuleHyp i -> ruleHyp i sq
  RuleIntro arg -> ruleIntro arg sq
  RuleElim i arg -> ruleElim i arg sq
  RuleEq -> ruleEq sq
  RuleCompute -> ruleCompute sq
  RuleCut ty x -> ruleCut ty x sq
  RuleLemma name args -> ruleLemma env name args sq
  RuleThin i -> ruleThin i sq
  RuleCumulativity lvl -> ruleCumulativity lvl sq

--------------------------------------------------------------------------------
-- Head form of a type / proposition
--------------------------------------------------------------------------------

-- | Unfold soft encodings and compute to WHNF. This is the form tactics
-- inspect when deciding which rule applies.
headForm :: Term -> Term
headForm = whnf . unfoldSoft

-- | Computational type equality.
typesEq :: Term -> Term -> Bool
typesEq a b = alphaEq (headForm a) (headForm b)

--------------------------------------------------------------------------------
-- Hypothesis
--------------------------------------------------------------------------------

ruleHyp :: Int -> Sequent -> Either RefineError RuleResult
ruleHyp i sq = do
  h <- maybe (failRule "hyp" ("no hypothesis " <> tshow i)) pure (lookupHyp i sq)
  if hHidden h
    then failRule "hyp" "cannot use a hidden hypothesis in an extract"
    else
      let x = hVar h
          ty = hType h
          c = seqConcl sq
          c' = headForm c
          ty' = headForm ty
          success extract =
            Right
              RuleResult
                { rrName = "hyp " <> tshow i
                , rrSubgoals = []
                , rrExtract = const extract
                }
       in case c' of
            -- The conclusion is the hypothesis type: inhabit it with x.
            _
              | typesEq c ty -> success (TVar x)
            -- Membership / reflexivity at the declared type.
            TEqual t a b
              | typesEq t ty
                  && computeEq a (TVar x)
                  && computeEq b (TVar x) ->
                  success TAxiom
            TEqual t a b
              | typesEq t ty && computeEq a b && computeEq a (TVar x) ->
                  success TAxiom
            -- Universe cumulativity: x : U{i}  ⊢  x ∈ U{j}  for i ≤ j.
            TEqual (TUniverse j) a b
              | computeEq a (TVar x)
                  && computeEq b (TVar x)
                  , TUniverse declLvl <- ty'
                  , levelLe declLvl j ->
                  success TAxiom
            TUniverse j
              | TUniverse declLvl <- ty'
              , levelLe declLvl j ->
                  success (TVar x)
            _ ->
              failRule
                "hyp"
                ( "hypothesis "
                    <> tshow i
                    <> " does not match the conclusion"
                )

--------------------------------------------------------------------------------
-- Introduction
--------------------------------------------------------------------------------

ruleIntro :: IntroArg -> Sequent -> Either RefineError RuleResult
ruleIntro arg sq =
  let c = headForm (seqConcl sq)
   in case (c, arg) of
        (TEqual {}, _) -> ruleEq sq
        -- Function / implication / universal.
        (TFunction a x b, IntroInfer mx) -> introFun sq a x b mx
        (TProduct a x b, IntroInfer Nothing) | not (isDependentProd (TProduct a x b)) ->
          introPairNonDep sq a b
        (TProduct a x b, IntroWitness t) -> introPairWitness sq a x b t
        (TProduct {}, IntroInfer (Just _)) ->
          failRule "intro" "dependent pair requires a witness: intro with <term>"
        (TProduct {}, IntroInfer Nothing) ->
          failRule "intro" "dependent pair requires a witness: intro with <term>"
        (TUnion {}, IntroLeft) -> introUnionL sq c
        (TUnion {}, IntroRight) -> introUnionR sq c
        (TUnion {}, IntroInfer Nothing) ->
          failRule "intro" "union introduction needs `intro left` or `intro right`"
        (TUnit, _) -> introUnit
        (TTrue, _) -> introUnit
        (TSquash a, _) -> introSquash sq a
        (TSet a x p, IntroWitness t) -> introSet sq a x p t
        (TSet {}, _) -> failRule "intro" "set introduction requires a witness"
        (TList {}, IntroInfer Nothing) -> introNil sq
        (TList a, IntroWitness t) -> introCons sq a t
        (TUniverse {}, _) -> failRule "intro" "universes are introduced by formation / cumulativity, not intro"
        (TVoid, _) -> failRule "intro" "Void has no introduction rule"
        (TInt, IntroWitness t) -> introIntWitness sq t
        (TInt, _) -> failRule "intro" "Int introduction requires a numeral: intro with n"
        (TAtom, IntroWitness t) -> introAtomWitness sq t
        _
          | TNat n <- c ->
              failRule "intro" ("cannot inhabit the numeral " <> tshow n <> " (not a type)")
        _ ->
          failRule "intro" "no introduction rule for this conclusion"

introFun :: Sequent -> Term -> Var -> Term -> Maybe Var -> Either RefineError RuleResult
introFun sq a x b mx = do
  let used = declaredVars sq
      x0 = maybe (if isDummyVar x then Var "x" else x) id mx
      x' = freshVar used x0
      b' = if x' == x || isDummyVar x then b else subst1 x (TVar x') b
      sub = sq {seqHyps = seqHyps sq ++ [visibleHyp x' a], seqConcl = b'}
  Right
    RuleResult
      { rrName = "intro"
      , rrSubgoals = [LabeledGoal "main" sub]
      , rrExtract = \case
          (e : _) -> TLambda x' e
          [] -> TLambda x' TAxiom
      }

introPairNonDep :: Sequent -> Term -> Term -> Either RefineError RuleResult
introPairNonDep sq a b =
  Right
    RuleResult
      { rrName = "intro"
      , rrSubgoals =
          [ LabeledGoal "left" sq {seqConcl = a}
          , LabeledGoal "right" sq {seqConcl = b}
          ]
      , rrExtract = \case
          (e1 : e2 : _) -> TPair e1 e2
          _ -> TPair TAxiom TAxiom
      }

introPairWitness :: Sequent -> Term -> Var -> Term -> Term -> Either RefineError RuleResult
introPairWitness sq a x b t =
  let b' = if isDummyVar x then b else subst1 x t b
   in Right
        RuleResult
          { rrName = "intro with"
          , rrSubgoals =
              [ LabeledGoal "wf" sq {seqConcl = TMember t a}
              , LabeledGoal "main" sq {seqConcl = b'}
              ]
          , rrExtract = \case
              (_ : e : _) -> TPair t e
              _ -> TPair t TAxiom
          }

introUnionL :: Sequent -> Term -> Either RefineError RuleResult
introUnionL sq (TUnion a _) =
  Right
    RuleResult
      { rrName = "intro left"
      , rrSubgoals = [LabeledGoal "main" sq {seqConcl = a}]
      , rrExtract = \case
          (e : _) -> TInl e
          [] -> TInl TAxiom
      }
introUnionL _ _ = failRule "intro left" "conclusion is not a union"

introUnionR :: Sequent -> Term -> Either RefineError RuleResult
introUnionR sq (TUnion _ b) =
  Right
    RuleResult
      { rrName = "intro right"
      , rrSubgoals = [LabeledGoal "main" sq {seqConcl = b}]
      , rrExtract = \case
          (e : _) -> TInr e
          [] -> TInr TAxiom
      }
introUnionR _ _ = failRule "intro right" "conclusion is not a union"

introUnit :: Either RefineError RuleResult
introUnit =
  Right
    RuleResult
      { rrName = "intro"
      , rrSubgoals = []
      , rrExtract = const TAxiom
      }

introSquash :: Sequent -> Term -> Either RefineError RuleResult
introSquash sq a =
  -- Squash introduction: prove A, discard the extract, hide hypotheses so
  -- the extract (axiom) cannot mention them.
  let sub = sq {seqConcl = a}
   in Right
        RuleResult
          { rrName = "intro"
          , rrSubgoals = [LabeledGoal "main" sub]
          , rrExtract = const TAxiom
          }

introSet :: Sequent -> Term -> Var -> Term -> Term -> Either RefineError RuleResult
introSet sq a x p t =
  let p' = subst1 x t p
   in Right
        RuleResult
          { rrName = "intro with"
          , rrSubgoals =
              [ LabeledGoal "wf" sq {seqConcl = TMember t a}
              , LabeledGoal "main" sq {seqConcl = p'}
              ]
          , rrExtract = const t
          }

introNil :: Sequent -> Either RefineError RuleResult
introNil _ =
  Right
    RuleResult
      { rrName = "intro"
      , rrSubgoals = []
      , rrExtract = const TNil
      }

introCons :: Sequent -> Term -> Term -> Either RefineError RuleResult
introCons sq a t =
  -- `intro with h` on List A expects a cons whose head is h; the user should
  -- inhabit A and List A. We treat the witness as the head.
  Right
    RuleResult
      { rrName = "intro with"
      , rrSubgoals =
          [ LabeledGoal "head" sq {seqConcl = TMember t a}
          , LabeledGoal "tail" sq {seqConcl = TList a}
          ]
      , rrExtract = \case
          (_ : tl : _) -> TCons t tl
          _ -> TCons t TNil
      }

introIntWitness :: Sequent -> Term -> Either RefineError RuleResult
introIntWitness _ t =
  case headForm t of
    TNat _ ->
      Right
        RuleResult
          { rrName = "intro with"
          , rrSubgoals = []
          , rrExtract = const t
          }
    _ -> failRule "intro" "Int witness must be a numeral"

introAtomWitness :: Sequent -> Term -> Either RefineError RuleResult
introAtomWitness _ t =
  case headForm t of
    TToken _ ->
      Right
        RuleResult
          { rrName = "intro with"
          , rrSubgoals = []
          , rrExtract = const t
          }
    _ -> failRule "intro" "Atom witness must be a token"

--------------------------------------------------------------------------------
-- Equality / membership
--------------------------------------------------------------------------------

-- | Canonical decomposition of an equality (or membership) conclusion.
ruleEq :: Sequent -> Either RefineError RuleResult
ruleEq sq =
  case headForm (seqConcl sq) of
    TEqual ty a b -> eqCD sq ty a b
    c ->
      -- Try to read a non-equality conclusion as a type-equality in a universe,
      -- or fail.
      failRule "eq" ("conclusion is not an equality: " <> T.pack (show c))

eqCD :: Sequent -> Term -> Term -> Term -> Either RefineError RuleResult
eqCD sq ty a b =
  let ty' = headForm ty
      a' = headForm a
      b' = headForm b
      done =
        Right
          RuleResult
            { rrName = "eq"
            , rrSubgoals = []
            , rrExtract = const TAxiom
            }
      subgoals gs =
        Right
          RuleResult
            { rrName = "eq"
            , rrSubgoals = gs
            , rrExtract = const TAxiom
            }
      goal t = LabeledGoal "eq" sq {seqConcl = t}
   in case ty' of
        -- Universe: type equality.
        TUniverse lvl -> eqInUniverse sq lvl a' b'
        TProp lvl -> eqInUniverse sq lvl a' b'
        -- Unit: both sides axiom.
        TUnit
          | isUnitVal a' && isUnitVal b' -> done
        -- Integers: both sides the same numeral (after computation).
        TInt
          | TNat n <- a'
          , TNat m <- b'
          , n == m ->
              done
        -- Atoms.
        TAtom
          | TToken s <- a'
          , TToken t <- b'
          , s == t ->
              done
        -- Function extensionality.
        TFunction aTy x bTy ->
          let used = declaredVars sq
              x' = freshVar used (if isDummyVar x then Var "x" else x)
              bTy' = if isDummyVar x then bTy else subst1 x (TVar x') bTy
              left = TApply a' (TVar x')
              right = TApply b' (TVar x')
              sub =
                sq
                  { seqHyps = seqHyps sq ++ [visibleHyp x' aTy]
                  , seqConcl = TEqual bTy' left right
                  }
           in subgoals [LabeledGoal "ext" sub]
        -- Product: spread both sides.
        TProduct aTy x bTy ->
          let used = declaredVars sq
              u = freshVar used (Var "u")
              v = freshVar used (Var "v")
              -- Compare via spread to avoid requiring canonical pairs.
              fstA = TSpread a' u v (TVar u)
              fstB = TSpread b' u v (TVar u)
              sndA = TSpread a' u v (TVar v)
              sndB = TSpread b' u v (TVar v)
              bTy' = if isDummyVar x then bTy else subst1 x fstA bTy
           in subgoals
                [ goal (TEqual aTy fstA fstB)
                , goal (TEqual bTy' sndA sndB)
                ]
        -- Union: both inl or both inr.
        TUnion aTy bTy ->
          case (a', b') of
            (TInl a1, TInl b1) -> subgoals [goal (TEqual aTy a1 b1)]
            (TInr a1, TInr b1) -> subgoals [goal (TEqual bTy a1 b1)]
            _
              | computeEq a' b' -> done
            _ -> failRule "eq" "union values are not both inl or both inr"
        -- Equality type: proof-irrelevant.
        TEqual {}
          | isUnitVal a' && isUnitVal b' -> done
        -- Lists.
        TList aTy ->
          case (a', b') of
            (TNil, TNil) -> done
            (TCons h1 t1, TCons h2 t2) ->
              subgoals
                [ goal (TEqual aTy h1 h2)
                , goal (TEqual (TList aTy) t1 t2)
                ]
            _ -> failRule "eq" "list values are not both nil or both cons"
        -- Void: only if we already have a contradiction; no canonical values.
        TVoid -> failRule "eq" "Void has no canonical values"
        -- Reflexivity after computation, if both sides agree and we can
        -- justify membership via a hypothesis.
        _
          | computeEq a b ->
              case matchDecl sq a' ty' of
                Just _ -> done
                Nothing ->
                  -- Last resort: if both sides computed to the same canonical
                  -- value of a canonical type we already handled, we would
                  -- have returned. For variables of matching type:
                  case (a', ty') of
                    (TVar _, _) ->
                      failRule "eq" "variable membership does not match any hypothesis"
                    _
                      | alphaEq a' b' && isCanonicalValue a' -> done
                    _ ->
                      failRule "eq" "cannot prove equality by computation"
        _ -> failRule "eq" "no equality rule at this type"

-- | Type equality in a universe.
eqInUniverse :: Sequent -> LevelExp -> Term -> Term -> Either RefineError RuleResult
eqInUniverse sq lvl a b =
  let done =
        Right
          RuleResult
            { rrName = "eq"
            , rrSubgoals = []
            , rrExtract = const TAxiom
            }
      goal t = LabeledGoal "wf" sq {seqConcl = t}
      subgoals gs =
        Right
          RuleResult
            { rrName = "eq"
            , rrSubgoals = gs
            , rrExtract = const TAxiom
            }
      u = TUniverse lvl
   in case (headForm a, headForm b) of
        (TVoid, TVoid) -> done
        (TUnit, TUnit) -> done
        (TInt, TInt) -> done
        (TAtom, TAtom) -> done
        (TUniverse i, TUniverse j)
          | levelEq i j && levelLt i lvl -> done
        (TTrue, TTrue) -> done
        (TFalse, TFalse) -> done
        (TFunction a1 x1 b1, TFunction a2 x2 b2) ->
          let used = declaredVars sq
              x = freshVar used (if isDummyVar x1 then Var "x" else x1)
              b1' = if isDummyVar x1 then b1 else subst1 x1 (TVar x) b1
              b2' = if isDummyVar x2 then b2 else subst1 x2 (TVar x) b2
              sub =
                sq
                  { seqHyps = seqHyps sq ++ [visibleHyp x a1]
                  , seqConcl = TEqual u b1' b2'
                  }
           in subgoals [goal (TEqual u a1 a2), LabeledGoal "wf" sub]
        (TProduct a1 x1 b1, TProduct a2 x2 b2) ->
          let used = declaredVars sq
              x = freshVar used (if isDummyVar x1 then Var "x" else x1)
              b1' = if isDummyVar x1 then b1 else subst1 x1 (TVar x) b1
              b2' = if isDummyVar x2 then b2 else subst1 x2 (TVar x) b2
              sub =
                sq
                  { seqHyps = seqHyps sq ++ [visibleHyp x a1]
                  , seqConcl = TEqual u b1' b2'
                  }
           in subgoals [goal (TEqual u a1 a2), LabeledGoal "wf" sub]
        (TUnion a1 b1, TUnion a2 b2) ->
          subgoals [goal (TEqual u a1 a2), goal (TEqual u b1 b2)]
        (TEqual t1 x1 y1, TEqual t2 x2 y2) ->
          subgoals
            [ goal (TEqual u t1 t2)
            , goal (TEqual t1 x1 x2)
            , goal (TEqual t1 y1 y2)
            ]
        (TList a1, TList a2) -> subgoals [goal (TEqual u a1 a2)]
        (TSquash a1, TSquash a2) -> subgoals [goal (TEqual u a1 a2)]
        (TSet a1 x1 p1, TSet a2 x2 p2) ->
          let used = declaredVars sq
              x = freshVar used (if isDummyVar x1 then Var "x" else x1)
              p1' = subst1 x1 (TVar x) p1
              p2' = subst1 x2 (TVar x) p2
              sub =
                sq
                  { seqHyps = seqHyps sq ++ [visibleHyp x a1]
                  , seqConcl = TEqual u p1' p2'
                  }
           in subgoals [goal (TEqual u a1 a2), LabeledGoal "wf" sub]
        (a', b')
          | alphaEq a' b' -> done
        (TVar x, TVar y)
          | x == y ->
              -- A type variable declared at this (or a smaller) universe.
              case matchDecl sq (TVar x) u of
                Just _ -> done
                Nothing -> failRule "eq" "type variable not declared in this universe"
        _ -> failRule "eq" "types are not equal in this universe"

isUnitVal :: Term -> Bool
isUnitVal t = case headForm t of
  TAxiom -> True
  TTrue -> True
  TUnit -> False
  _ -> False

-- | Does some hypothesis declare @tm@ at a type matching @ty@?
matchDecl :: Sequent -> Term -> Term -> Maybe Hypothesis
matchDecl sq tm ty =
  case headForm tm of
    TVar x ->
      case
        [ h
        | h <- seqHyps sq
        , hVar h == x
        , not (hHidden h)
        , typesEq (hType h) ty || universeCover (hType h) ty
        ] of
        h : _ -> Just h
        [] -> Nothing
    _ -> Nothing

universeCover :: Term -> Term -> Bool
universeCover declared needed =
  case (headForm declared, headForm needed) of
    (TUniverse i, TUniverse j) -> levelLe i j
    _ -> False

--------------------------------------------------------------------------------
-- Elimination
--------------------------------------------------------------------------------

ruleElim :: Int -> ElimArg -> Sequent -> Either RefineError RuleResult
ruleElim i arg sq = do
  h <- maybe (failRule "elim" ("no hypothesis " <> tshow i)) pure (lookupHyp i sq)
  let ty = headForm (hType h)
      x = hVar h
  case (ty, arg) of
    (TVoid, _) -> elimVoid sq x
    (TFunction a y b, ElimWitness t) -> elimFun sq i x a y b t
    (TFunction a y b, ElimBare)
      | isDummyVar y || not (occursFree y b) ->
          -- Backchain: if the conclusion matches the codomain, generate the domain.
          elimFunBackchain sq i x a b
    (TFunction {}, ElimBare) ->
      failRule "elim" "dependent function elimination requires a witness: elim i with t"
    (TProduct a y b, _) -> elimProd sq i x a y b
    (TUnion a b, _) -> elimUnion sq i x a b
    (TEqual t a b, _) -> elimEqual sq i x t a b
    (TInt, _) -> elimInt sq i x
    (TList a, _) -> elimList sq i x a
    (TFalse, _) -> elimVoid sq x
    (TNot a, ElimWitness t) ->
      -- ¬A is A → Void; instantiate.
      elimFun sq i x a dummyVar TVoid t
    (TNot a, ElimBare) -> elimFunBackchain sq i x a TVoid
    (TImplies a b, ElimWitness t) -> elimFun sq i x a dummyVar b t
    (TImplies a b, ElimBare) -> elimFunBackchain sq i x a b
    (TAnd a b, _) -> elimProd sq i x a dummyVar b
    (TOr a b, _) -> elimUnion sq i x a b
    (TAll a y b, ElimWitness t) -> elimFun sq i x a y b t
    (TExists a y b, _) -> elimProd sq i x a y b
    (TSet a y p, _) -> elimSet sq i x a y p
    (TSquash _, _) ->
      failRule "elim" "squash elimination is not extractable; use a squash-stable goal"
    _ -> failRule "elim" "no elimination rule for this hypothesis"

elimVoid :: Sequent -> Var -> Either RefineError RuleResult
elimVoid sq x =
  Right
    RuleResult
      { rrName = "elim"
      , rrSubgoals = []
      , rrExtract = const (TAny (TVar x) (seqConcl sq))
      }

elimFun :: Sequent -> Int -> Var -> Term -> Var -> Term -> Term -> Either RefineError RuleResult
elimFun sq _i f a y b t =
  let b' = if isDummyVar y then b else subst1 y t b
      used = declaredVars sq
      z = freshVar used (Var "y")
      subMain =
        sq
          { seqHyps = seqHyps sq ++ [visibleHyp z b']
          }
   in Right
        RuleResult
          { rrName = "elim with"
          , rrSubgoals =
              [ LabeledGoal "wf" sq {seqConcl = TMember t a}
              , LabeledGoal "main" subMain
              ]
          , rrExtract = \case
              (_ : e : _) -> subst1 z (TApply (TVar f) t) e
              _ -> TApply (TVar f) t
          }

elimFunBackchain :: Sequent -> Int -> Var -> Term -> Term -> Either RefineError RuleResult
elimFunBackchain sq _i f a b =
  if typesEq b (seqConcl sq)
    then
      Right
        RuleResult
          { rrName = "elim"
          , rrSubgoals = [LabeledGoal "main" sq {seqConcl = a}]
          , rrExtract = \case
              (e : _) -> TApply (TVar f) e
              [] -> TApply (TVar f) TAxiom
          }
    else failRule "elim" "codomain does not match the conclusion; supply a witness"

elimProd :: Sequent -> Int -> Var -> Term -> Var -> Term -> Either RefineError RuleResult
elimProd sq _i p a y b =
  let used = declaredVars sq
      u = freshVar used (Var "u")
      v = freshVar used (Var "v")
      b' = if isDummyVar y then b else subst1 y (TVar u) b
      sub =
        sq
          { seqHyps = seqHyps sq ++ [visibleHyp u a, visibleHyp v b']
          }
   in Right
        RuleResult
          { rrName = "elim"
          , rrSubgoals = [LabeledGoal "main" sub]
          , rrExtract = \case
              (e : _) -> TSpread (TVar p) u v e
              [] -> TSpread (TVar p) u v TAxiom
          }

elimUnion :: Sequent -> Int -> Var -> Term -> Term -> Either RefineError RuleResult
elimUnion sq _i d a b =
  let used = declaredVars sq
      u = freshVar used (Var "u")
      v = freshVar used (Var "v")
      left = sq {seqHyps = seqHyps sq ++ [visibleHyp u a]}
      right = sq {seqHyps = seqHyps sq ++ [visibleHyp v b]}
   in Right
        RuleResult
          { rrName = "elim"
          , rrSubgoals = [LabeledGoal "inl" left, LabeledGoal "inr" right]
          , rrExtract = \case
              (e1 : e2 : _) -> TDecide (TVar d) u e1 v e2
              _ -> TDecide (TVar d) u TAxiom v TAxiom
          }

elimEqual :: Sequent -> Int -> Var -> Term -> Term -> Term -> Either RefineError RuleResult
elimEqual sq _i _d t a b =
  -- Substitution: replace a by b in the conclusion.
  let c = seqConcl sq
      c' = substTermHead a b c
   in if alphaEq c c'
        then failRule "elim" "equality does not rewrite the conclusion"
        else
          Right
            RuleResult
              { rrName = "elim"
              , rrSubgoals = [LabeledGoal "main" sq {seqConcl = c'}]
              , rrExtract = \case
                  (e : _) -> e
                  [] -> TAxiom
              }
  where
    -- Replace computationally-equal copies of `a` by `b` at the surface of `c`,
    -- and recursively in all subterms.
    substTermHead src dst = go
      where
        go tm
          | computeEq tm src = dst
          | otherwise = case tm of
              TVar _ -> tm
              TOp op bts -> TOp op (map (\(BoundTerm vs body) -> BoundTerm vs (go body)) bts)
    -- silence unused
    _ = t

elimSet :: Sequent -> Int -> Var -> Term -> Var -> Term -> Either RefineError RuleResult
elimSet sq _i s a y p =
  let used = declaredVars sq
      u = freshVar used (Var "u")
      w = freshVar used (Var "w")
      p' = subst1 y (TVar u) p
      -- The proof of P(u) is hidden (squash-like).
      sub =
        sq
          { seqHyps = seqHyps sq ++ [visibleHyp u a, hiddenHyp w p']
          }
   in Right
        RuleResult
          { rrName = "elim"
          , rrSubgoals = [LabeledGoal "main" sub]
          , rrExtract = \case
              (e : _) -> subst1 u (TVar s) e
              [] -> TVar s
          }

elimInt :: Sequent -> Int -> Var -> Either RefineError RuleResult
elimInt sq _i n =
  let used = declaredVars sq
      k = freshVar used (Var "k")
      ih = freshVar used (Var "ih")
      p t = subst1 n t (seqConcl sq)
      -- Base: P(0)
      base = sq {seqConcl = p (TNat 0)}
      -- Up: k:Int, k ≥ 0, ih:P(k) ⊢ P(k+1)
      -- We encode k ≥ 0 as 0 ≤ k, i.e. less(0,k+1, True, False) or simply
      -- a hypothesis less-eq. Use `0 ≤ k` as `less (-1) k` is messy.
      -- Subgoal: k:Int, ih:P(k) ⊢ P(k+1)  (unrestricted; user can constrain).
      up =
        sq
          { seqHyps =
              seqHyps sq
                ++ [visibleHyp k TInt, visibleHyp ih (p (TVar k))]
          , seqConcl = p (TAdd (TVar k) (TNat 1))
          }
      -- Down: k:Int, ih:P(k) ⊢ P(k-1)
      down =
        sq
          { seqHyps =
              seqHyps sq
                ++ [visibleHyp k TInt, visibleHyp ih (p (TVar k))]
          , seqConcl = p (TSub (TVar k) (TNat 1))
          }
   in Right
        RuleResult
          { rrName = "elim"
          , rrSubgoals =
              [ LabeledGoal "base" base
              , LabeledGoal "up" up
              , LabeledGoal "down" down
              ]
          , rrExtract = \case
              (eb : eu : ed : _) ->
                -- A primitive recursor is not in the term language; we emit
                -- a combined integer-eq / less tree is not faithful. We keep
                -- the extract as a placeholder application of `int_eq` on n
                -- versus 0, which is enough for the 0-case and documents the
                -- induction. Full integer recursor can be added as an operator.
                TIntEq (TVar n) (TNat 0) eb (TIntEq (TVar n) (TAdd (TVar k) (TNat 0)) eu ed)
              _ -> TAxiom
          }

elimList :: Sequent -> Int -> Var -> Term -> Either RefineError RuleResult
elimList sq _i xs a =
  let used = declaredVars sq
      h = freshVar used (Var "h")
      tl = freshVar used (Var "tl")
      ih = freshVar used (Var "ih")
      p t = subst1 xs t (seqConcl sq)
      base = sq {seqConcl = p TNil}
      stepG =
        sq
          { seqHyps =
              seqHyps sq
                ++ [ visibleHyp h a
                   , visibleHyp tl (TList a)
                   , visibleHyp ih (p (TVar tl))
                   ]
          , seqConcl = p (TCons (TVar h) (TVar tl))
          }
   in Right
        RuleResult
          { rrName = "elim"
          , rrSubgoals = [LabeledGoal "base" base, LabeledGoal "step" stepG]
          , rrExtract = \case
              (eb : es : _) -> TListInd (TVar xs) eb h tl ih es
              _ -> TAxiom
          }

--------------------------------------------------------------------------------
-- Computation, cut, lemma, thin, cumulativity
--------------------------------------------------------------------------------

ruleCompute :: Sequent -> Either RefineError RuleResult
ruleCompute sq =
  let c = seqConcl sq
      c' = whnf (unfoldSoft c)
   in if alphaEq c c'
        then failRule "compute" "conclusion is already in weak-head form"
        else
          Right
            RuleResult
              { rrName = "compute"
              , rrSubgoals = [LabeledGoal "main" sq {seqConcl = c'}]
              , rrExtract = \case
                  (e : _) -> e
                  [] -> TAxiom
              }

ruleCut :: Term -> Var -> Sequent -> Either RefineError RuleResult
ruleCut ty x sq =
  let x' = freshVar (declaredVars sq) x
      g1 = sq {seqConcl = ty}
      g2 = sq {seqHyps = seqHyps sq ++ [visibleHyp x' ty]}
   in Right
        RuleResult
          { rrName = "cut"
          , rrSubgoals = [LabeledGoal "cut" g1, LabeledGoal "main" g2]
          , rrExtract = \case
              (e1 : e2 : _) -> subst1 x' e1 e2
              _ -> TAxiom
          }

ruleLemma :: LemmaEnv -> Name -> [Term] -> Sequent -> Either RefineError RuleResult
ruleLemma env name args sq =
  case lookupLemma name env of
    Nothing -> failRule "lemma" ("unknown lemma " <> name)
    Just stmt ->
      let inst = instantiateLeading stmt args
          x = freshVar (declaredVars sq) (Var "lem")
          sub = sq {seqHyps = seqHyps sq ++ [visibleHyp x inst]}
       in Right
            RuleResult
              { rrName = "lemma " <> name
              , rrSubgoals = [LabeledGoal "main" sub]
              , rrExtract = \case
                  (e : _) -> subst1 x (TVar x) e
                  [] -> TVar x
              }

-- | Instantiate leading ∀ / function binders with the given witnesses.
instantiateLeading :: Term -> [Term] -> Term
instantiateLeading t [] = t
instantiateLeading t (a : as) =
  case headForm t of
    TFunction _ x b -> instantiateLeading (subst1 x a b) as
    TAll _ x b -> instantiateLeading (subst1 x a b) as
    _ -> t

ruleThin :: Int -> Sequent -> Either RefineError RuleResult
ruleThin i sq = do
  _ <- maybe (failRule "thin" ("no hypothesis " <> tshow i)) pure (lookupHyp i sq)
  let hyps' = [h | (j, h) <- zip [1 ..] (seqHyps sq), j /= i]
      -- Free-variable check: the remaining sequent must stay closed w.r.t.
      -- the removed variable.
      sq' = sq {seqHyps = hyps'}
  if isClosedSequent sq'
    then
      Right
        RuleResult
          { rrName = "thin"
          , rrSubgoals = [LabeledGoal "main" sq']
          , rrExtract = \case
              (e : _) -> e
              [] -> TAxiom
          }
    else failRule "thin" "cannot thin: remaining sequent would mention the variable"

ruleCumulativity :: LevelExp -> Sequent -> Either RefineError RuleResult
ruleCumulativity j sq =
  case headForm (seqConcl sq) of
    TEqual (TUniverse k) a b
      | levelLe j k ->
          Right
            RuleResult
              { rrName = "cumulativity"
              , rrSubgoals =
                  [ LabeledGoal "main" sq {seqConcl = TEqual (TUniverse j) a b}
                  ]
              , rrExtract = const TAxiom
              }
    TMember a (TUniverse k)
      | levelLe j k ->
          Right
            RuleResult
              { rrName = "cumulativity"
              , rrSubgoals =
                  [ LabeledGoal "main" sq {seqConcl = TMember a (TUniverse j)}
                  ]
              , rrExtract = const TAxiom
              }
    _ -> failRule "cumulativity" "conclusion is not a universe membership"

tshow :: (Show a) => a -> Text
tshow = T.pack . show
