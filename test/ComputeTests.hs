module ComputeTests (computeTests) where

import Test.Tasty
import Test.Tasty.HUnit

import Nuprl.Compute
import Nuprl.Subst
import Nuprl.Term

computeTests :: TestTree
computeTests =
  testGroup
    "Compute"
    [ testCase "β-reduction" $ do
        let t = tApply (tLambda (Var "x") (TVar (Var "x"))) (tNat 3)
        assertBool "id 3 → 3" (alphaEq (whnf t) (tNat 3))
    , testCase "integer arithmetic" $ do
        whnf (tAdd (tNat 1) (tNat 2)) @?= tNat 3
        whnf (tMul (tNat 4) (tNat 5)) @?= tNat 20
        whnf (tSub (tNat 10) (tNat 3)) @?= tNat 7
    , testCase "spread" $ do
        let t = tSpread (Var "x") (Var "y") (tPair (tNat 1) (tNat 2)) (tAdd (TVar (Var "x")) (TVar (Var "y")))
        assertBool "spread pair" (alphaEq (whnf t) (tNat 3))
    , testCase "decide inl" $ do
        let t = tDecide (Var "x") (Var "y") (tInl (tNat 4)) (TVar (Var "x")) (TVar (Var "y"))
        assertBool "decide inl" (alphaEq (whnf t) (tNat 4))
    , testCase "soft unfold True" $ do
        unfoldSoft TTrue @?= TUnit
        unfoldSoft (TNot TTrue) @?= tArrow TTrue TVoid
    , testCase "list induction nil" $ do
        let t = tListInd (Var "h") (Var "t") (Var "ih") TNil (tNat 0) (tNat 1)
        assertBool "nil" (alphaEq (whnf t) (tNat 0))
    , testCase "int_eq" $ do
        -- True/False unfold to Unit/Void during reduction.
        whnf (tIntEq (tNat 1) (tNat 1) TTrue TFalse) @?= TUnit
        whnf (tIntEq (tNat 1) (tNat 2) TTrue TFalse) @?= TVoid
    , testCase "closed less-than computes to Unit or Void" $ do
        whnf (tLt (tNat 0) (tNat 1)) @?= TUnit
        whnf (tLt (tNat 1) (tNat 0)) @?= TVoid
        whnf (tLt (tNat 2) (tNat 2)) @?= TVoid
    ]
