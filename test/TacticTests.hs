module TacticTests (tacticTests) where

import Data.Text (Text)
import Test.Tasty
import Test.Tasty.HUnit

import Nuprl.Check
import Nuprl.Error
import Nuprl.Library
import Nuprl.Parse
import Nuprl.Tactic
import Nuprl.Term

mustParse :: Text -> Term
mustParse txt =
  case parseTerm txt of
    Right t -> t
    Left e -> error (show (prettyError e))

mustTac :: Text -> TacticExpr
mustTac txt =
  case parseTactic txt of
    Right t -> t
    Left e -> error (show (prettyError e))

tacticTests :: TestTree
tacticTests =
  testGroup
    "Tactic"
    [ testCase "identity: ∀A:U{i}. A → A" $ do
        let g = mustParse "∀A:U{i}. A → A"
            tx = mustTac "intro A; intro x; hyp"
        case prove coreLibrary g tx of
          Left e -> assertFailure (show (prettyError e))
          Right extr ->
            case extr of
              TLambda _ (TLambda _ (TVar _)) -> pure ()
              other -> assertFailure ("extract " <> show other)
    , testCase "const: A → B → A" $ do
        let g = mustParse "∀A:U{i}. ∀B:U{i}. A → B → A"
            tx = mustTac "intro A; intro B; intro x; intro y; hyp 3"
        case prove coreLibrary g tx of
          Left e -> assertFailure (show (prettyError e))
          Right _ -> pure ()
    , testCase "True is inhabited" $ do
        let g = mustParse "True"
            tx = mustTac "intro"
        case prove coreLibrary g tx of
          Left e -> assertFailure (show (prettyError e))
          Right extr -> extr @?= TAxiom
    , testCase "conjunction intro" $ do
        let g = mustParse "True ∧ True"
            tx = mustTac "intro; intro; intro"
        case prove coreLibrary g tx of
          Left e -> assertFailure (show (prettyError e))
          Right _ -> pure ()
    , testCase "1+1 = 2 ∈ Int" $ do
        let g = mustParse "1 + 1 = 2 ∈ Int"
            tx = mustTac "eq"
        case prove coreLibrary g tx of
          Left e -> assertFailure (show (prettyError e))
          Right extr -> extr @?= TAxiom
    , testCase "auto on identity" $ do
        let g = mustParse "∀A:U{i}. A → A"
            tx = mustTac "auto"
        case prove coreLibrary g tx of
          Left e -> assertFailure (show (prettyError e))
          Right _ -> pure ()
    , testCase "0 < 1 by computation" $ do
        let g = mustParse "0 < 1"
            tx = mustTac "intro"
        case prove coreLibrary g tx of
          Left e -> assertFailure (show (prettyError e))
          Right _ -> pure ()
    , testCase "set membership 1 ∈ {s:Int | 0 < s}" $ do
        let g = mustParse "1 ∈ {s:Int | 0 < s}"
            tx = mustTac "auto"
        case prove coreLibrary g tx of
          Left e -> assertFailure (show (prettyError e))
          Right _ -> pure ()
    , testCase "integer equality is decidable" $ do
        let g = mustParse "∀x:Int. ∀y:Int. x = y ∈ Int ∨ ¬(x = y ∈ Int)"
            tx = mustTac "intro x; intro y; decide x = y THENL [left THEN hyp, right THEN hyp]"
        case prove coreLibrary g tx of
          Left e -> assertFailure (show (prettyError e))
          Right _ -> pure ()
    , testCase "inl and inr are disjoint" $ do
        let g = mustParse "¬(inl Ax = inr Ax ∈ True ⊎ True)"
            tx = mustTac "intro p; elim 1"
        case prove coreLibrary g tx of
          Left e -> assertFailure (show (prettyError e))
          Right _ -> pure ()
    , testCase "equipollence of a type with itself" $ do
        let g = mustParse "∀A:U{i}. ∃f:(A → A). ∃g:(A → A). (∀x:A. g (f x) = x ∈ A) ∧ (∀y:A. f (g y) = y ∈ A)"
            tx = mustTac "intro A; exists (λx. x) THENL [auto, exists (λx. x) THENL [auto, split THENL [intro x THEN auto, intro y THEN auto]]]"
        case prove coreLibrary g tx of
          Left e -> assertFailure (show (prettyError e))
          Right _ -> pure ()
    ]
