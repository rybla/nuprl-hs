module SubstTests (substTests) where

import Data.Set qualified as Set
import Test.Tasty
import Test.Tasty.HUnit

import Nuprl.Subst
import Nuprl.Term

x, y :: Var
x = Var "x"
y = Var "y"

idLam :: Term
idLam = tLambda x (TVar x)

substTests :: TestTree
substTests =
  testGroup
    "Subst"
    [ testCase "free vars of an application" $ do
        freeVars (tApply (TVar x) (TVar y)) @?= Set.fromList [x, y]
    , testCase "lambda binds" $ do
        freeVars idLam @?= Set.empty
    , testCase "capture-avoiding substitution" $ do
        -- (λx. y)[y := x]  should be  λx'. x, not λx. x
        let body = tLambda x (TVar y)
            result = subst1 y (TVar x) body
        case result of
          TLambda x' (TVar v) -> do
            assertBool "binder freshened" (x' /= x || v /= x)
            v @?= x
            assertBool "no capture" (x' /= v)
          other -> assertFailure ("unexpected " <> show other)
    , testCase "α-equivalence of renamed lambdas" $ do
        let t1 = tLambda x (TVar x)
            t2 = tLambda y (TVar y)
        assertBool "id α-eq" (alphaEq t1 t2)
    , testCase "α-inequality of free vars" $ do
        assertBool "x /= y" (not (alphaEq (TVar x) (TVar y)))
    , testCase "matching a function pattern" $ do
        let pat = tApply (TVar x) (TVar y)
            tm = tApply (tNat 1) (tNat 2)
        case matchTerm (Set.fromList [x, y]) pat tm of
          Just s -> do
            subst s (TVar x) @?= tNat 1
            subst s (TVar y) @?= tNat 2
          Nothing -> assertFailure "match failed"
    , testCase "freshVar avoids the set" $ do
        let v = freshVar (Set.fromList [x]) x
        assertBool "different" (v /= x)
    ]
