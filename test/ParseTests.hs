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
              , "7 % 2"
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
    , testCase "squash vs list brackets" $ do
        case mustParse "[True]" of
          TSquash TTrue -> pure ()
          other -> assertFailure ("squash " <> show other)
        case mustParse "[]" of
          TNil -> pure ()
          other -> assertFailure ("nil " <> show other)
        case mustParse "[1, 2]" of
          TCons (TNat 1) (TCons (TNat 2) TNil) -> pure ()
          other -> assertFailure ("list " <> show other)
    , testCase "quotient type" $ do
        let t = mustParse "(x,y):Int // (x % 2) = (y % 2) ∈ Int"
        case t of
          TQuotient TInt (Var "x") (Var "y") _ -> pure ()
          other -> assertFailure (show other)
        case mustParse "Int // True" of
          TQuotient TInt x y TTrue | isDummyVar x && isDummyVar y -> pure ()
          other -> assertFailure (show other)
        let t0 = mustParse "(x,y):Int // x = y ∈ Int"
            s = renderTerm t0
            t1 = mustParse s
         in assertBool (show s) (alphaEq t0 t1)
    , testCase "set type" $ do
        let t = mustParse "{s:Int | 0 < s ∧ s < n + 1}"
        case t of
          TSet TInt (Var "s") _ -> pure ()
          other -> assertFailure (show other)
    , testCase "dependent intersection" $ do
        let t = mustParse "⋂A:U{i}. A → A"
        case t of
          TIsect (TUniverse (LVar "i")) (Var "A") body ->
            case body of
              TFunction (TVar (Var "A")) _ (TVar (Var "A")) -> pure ()
              other -> assertFailure ("body " <> show other)
          other -> assertFailure (show other)
    , testCase "independent intersection" $ do
        let t = mustParse "Int ∩ Unit"
        case t of
          TIsect TInt x TUnit | isDummyVar x -> pure ()
          other -> assertFailure (show other)
    , testCase "ASCII intersection" $ do
        let t = mustParse "isect A:U{i}. A → A"
        case t of
          TIsect (TUniverse (LVar "i")) (Var "A") _ -> pure ()
          other -> assertFailure (show other)
        case mustParse "Int cap Unit" of
          TIsect TInt x TUnit | isDummyVar x -> pure ()
          other -> assertFailure (show other)
    , testCase "uniform isect" $ do
        let t = mustParse "isect(Int; x. x = x ∈ Int)"
        case t of
          TIsect TInt (Var "x") _ -> pure ()
          other -> assertFailure (show other)
    , testCase "intersection pretty-print roundtrip" $ do
        let originals =
              [ "⋂A:U{i}. A → A"
              , "Int ∩ Unit"
              ]
        mapM_
          ( \s ->
              let t = mustParse s
                  s' = renderTerm t
                  t' = mustParse s'
               in assertBool (show s <> " -> " <> show s') (alphaEq t t')
          )
          originals
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
    , testCase "integer induction surface syntax" $ do
        let t = mustParse "ind(3; x,ih. 0; 0; k,r. r + 1)"
        case t of
          TInd (TNat 3) _ _ _ (TNat 0) _ _ _ -> pure ()
          other -> assertFailure (show other)
    ]
