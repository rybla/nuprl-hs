module ParseTests (parseTests) where

import Data.Text (Text)
import Test.Tasty
import Test.Tasty.HUnit

import Nuprl.Error
import Nuprl.Parse
import Nuprl.Pretty
import Nuprl.Subst
import Nuprl.Term

mustParse :: Text -> Term
mustParse txt =
  case parseTerm txt of
    Right t -> t
    Left e -> error (show (prettyError e))

parseTests :: TestTree
parseTests =
  testGroup
    "Parse"
    [ testCase "identity lambda" $ do
        let t = mustParse "λx. x"
        assertBool "α-eq" (alphaEq t (tLambda (Var "x") (TVar (Var "x"))))
    , testCase "non-dependent arrow" $ do
        let t = mustParse "Int → Int"
        case t of
          TFunction TInt x TInt | isDummyVar x -> pure ()
          other -> assertFailure (show other)
    , testCase "forall" $ do
        let t = mustParse "∀A:U{i}. A → A"
        case t of
          TAll (TUniverse (LVar "i")) (Var "A") body ->
            case body of
              TFunction (TVar (Var "A")) _ (TVar (Var "A")) -> pure ()
              other -> assertFailure ("body " <> show other)
          other -> assertFailure (show other)
    , testCase "equality" $ do
        let t = mustParse "1 = 1 ∈ Int"
        case t of
          TEqual TInt (TNat 1) (TNat 1) -> pure ()
          other -> assertFailure (show other)
    , testCase "membership" $ do
        let t = mustParse "0 ∈ Int"
        case t of
          TMember (TNat 0) TInt -> pure ()
          other -> assertFailure (show other)
    , testCase "and / or / implies" $ do
        let t = mustParse "True ∧ False ⇒ True"
        case t of
          TImplies (TAnd TTrue TFalse) TTrue -> pure ()
          other -> assertFailure (show other)
    , testCase "pretty-print roundtrip of closed combinators" $ do
        let originals =
              [ "λx. x"
              , "Int → Int"
              , "True ∧ False"
              , "1 + 2 * 3"
              , "inl Ax"
              ]
        mapM_
          ( \s ->
              let t = mustParse s
                  s' = renderTerm t
                  t' = mustParse s'
               in assertBool (show s <> " -> " <> show s') (alphaEq t t')
          )
          originals
    , testCase "tactic script" $ do
        case parseTactic "intro A THEN intro x THEN hyp" of
          Right _ -> pure ()
          Left e -> assertFailure (show (prettyError e))
    , testCase "nested negation" $ do
        let t = mustParse "¬¬True"
        case t of
          TNot (TNot TTrue) -> pure ()
          other -> assertFailure (show other)
    , testCase "integer less-than type" $ do
        let t = mustParse "0 < 1"
        case t of
          TLt (TNat 0) (TNat 1) -> pure ()
          other -> assertFailure (show other)
    , testCase "set type" $ do
        let t = mustParse "{s:Int | 0 < s ∧ s < n + 1}"
        case t of
          TSet TInt (Var "s") _ -> pure ()
          other -> assertFailure (show other)
    , testCase "juxtaposition is application, not a uniform operator" $ do
        let t = mustParse "g (f x)"
        case t of
          TApply (TVar (Var "g")) (TApply (TVar (Var "f")) (TVar (Var "x"))) -> pure ()
          other -> assertFailure (show other)
    , testCase "capitalised uniform operator" $ do
        let t = mustParse "Fin(n)"
        case t of
          TOp (Operator (OpId "Fin") []) [BoundTerm [] (TVar (Var "n"))] -> pure ()
          other -> assertFailure (show other)
    ]
