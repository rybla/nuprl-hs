module TermTests (termTests) where

import Test.Tasty
import Test.Tasty.HUnit

import Nuprl.Term

termTests :: TestTree
termTests =
  testGroup
    "Term"
    [ testCase "smart constructors agree with patterns" $ do
        case tArrow tInt tInt of
          TFunction TInt x TInt | isDummyVar x -> pure ()
          other -> assertFailure ("unexpected " <> show other)
    , testCase "lambda pattern" $ do
        let t = tLambda (Var "x") (TVar (Var "x"))
        case t of
          TLambda x (TVar y) -> x @?= y
          _ -> assertFailure "not a lambda"
    , testCase "universe level pretty-print" $ do
        prettyLevel (LAdd (LVar "i") 1) @?= "i'"
        prettyLevel (LConst 1) @?= "1"
    , testCase "level inequality is conservative" $ do
        assertBool "1 < 2" (levelLt (LConst 1) (LConst 2))
        assertBool "i < i'" (levelLt (LVar "i") (levelSucc (LVar "i")))
        assertBool "i </ 5" (not (levelLt (LVar "i") (LConst 5)))
        assertBool "i ≤ i" (levelLe (LVar "i") (LVar "i"))
    , testCase "hidden variables" $ do
        assertBool "%" (isHiddenVar (Var "%x"))
        assertBool "not hidden" (not (isHiddenVar (Var "x")))
    , testCase "canonical classification" $ do
        assertBool "Int is a type" (isCanonicalType tInt)
        assertBool "λ is a value" (isCanonicalValue (tLambda (Var "x") (TVar (Var "x"))))
        assertBool "apply is not canonical" (not (isCanonicalValue (tApply (TVar (Var "f")) (TVar (Var "a")))))
    ]
