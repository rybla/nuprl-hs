module RuleTests (ruleTests) where

import Test.Tasty
import Test.Tasty.HUnit

import Nuprl.Rule
import Nuprl.Sequent
import Nuprl.Term

ruleTests :: TestTree
ruleTests =
  testGroup
    "Rule"
    [ testCase "hyp inhabits a declared type" $ do
        let sq =
              Sequent
                [visibleHyp (Var "x") tInt]
                tInt
        case applyRule emptyLemmaEnv (RuleHyp 1) sq of
          Right rr -> do
            null (rrSubgoals rr) @?= True
            rrExtract rr [] @?= TVar (Var "x")
          Left e -> assertFailure (show e)
    , testCase "intro on A → A" $ do
        let a = TVar (Var "A")
            sq = emptySequent (tArrow a a)
        case applyRule emptyLemmaEnv (RuleIntro (IntroInfer (Just (Var "x")))) sq of
          Right rr -> do
            length (rrSubgoals rr) @?= 1
            let sub = case rrSubgoals rr of
                  g : _ -> lgSequent g
                  [] -> error "no subgoals"
            seqConcl sub @?= a
            length (seqHyps sub) @?= 1
          Left e -> assertFailure (show e)
    , testCase "unit introduction" $ do
        case applyRule emptyLemmaEnv (RuleIntro (IntroInfer Nothing)) (emptySequent tUnit) of
          Right rr -> do
            null (rrSubgoals rr) @?= True
            rrExtract rr [] @?= TAxiom
          Left e -> assertFailure (show e)
    , testCase "1 = 1 ∈ Int by eq" $ do
        let sq = emptySequent (tEqual tInt (tNat 1) (tNat 1))
        case applyRule emptyLemmaEnv RuleEq sq of
          Right rr -> null (rrSubgoals rr) @?= True
          Left e -> assertFailure (show e)
    , testCase "void elim" $ do
        let sq =
              Sequent
                [visibleHyp (Var "x") tVoid]
                tInt
        case applyRule emptyLemmaEnv (RuleElim 1 ElimBare) sq of
          Right rr -> null (rrSubgoals rr) @?= True
          Left e -> assertFailure (show e)
    , testCase "closed sequent" $ do
        isClosedSequent (emptySequent (tArrow tInt tInt)) @?= True
        isClosedSequent (emptySequent (TVar (Var "A"))) @?= False
    , testCase "isect intro hides the index and does not λ-abstract" $ do
        let sq = emptySequent (tIsect dummyVar tUnit tUnit)
        case applyRule emptyLemmaEnv (RuleIntro (IntroInfer Nothing)) sq of
          Right rr -> do
            length (rrSubgoals rr) @?= 1
            let sub = case rrSubgoals rr of
                  g : _ -> lgSequent g
                  [] -> error "no subgoals"
            seqConcl sub @?= tUnit
            case seqHyps sub of
              [h] -> hHidden h @?= True
              hs -> assertFailure ("expected one hidden hyp, got " <> show (length hs))
            rrExtract rr [tAxiom] @?= tAxiom
          Left e -> assertFailure (show e)
    , testCase "quotient intro extracts the representative" $ do
        let q = tQuotient dummyVar dummyVar tInt tTrue
            sq = emptySequent q
        case applyRule emptyLemmaEnv (RuleIntro (IntroWitness (tNat 0))) sq of
          Right rr -> do
            length (rrSubgoals rr) @?= 1
            rrExtract rr [] @?= tNat 0
          Left e -> assertFailure (show e)
    , testCase "isect elim instantiates without applying" $ do
        let isectTy = tIsect dummyVar tUnit tInt
            sq =
              Sequent
                [visibleHyp (Var "f") isectTy]
                tInt
        case applyRule emptyLemmaEnv (RuleElim 1 (ElimWitness tAxiom)) sq of
          Right rr -> do
            length (rrSubgoals rr) @?= 2
            rrExtract rr [tAxiom, TVar (Var "y")] @?= TVar (Var "f")
          Left e -> assertFailure (show e)
    ]
