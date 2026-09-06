-- | Tasty test suite, organised by implementation stage.
module Main (main) where

import Test.Tasty

import ComputeTests (computeTests)
import ExampleTests (exampleTests)
import ParseTests (parseTests)
import RuleTests (ruleTests)
import SubstTests (substTests)
import TacticTests (tacticTests)
import TermTests (termTests)

main :: IO ()
main =
  defaultMain $
    testGroup
      "nuprl-hs"
      [ testGroup "stage 1 — terms" [termTests]
      , testGroup "stage 2 — substitution & α-equivalence" [substTests]
      , testGroup "stage 3 — parser & pretty-printer" [parseTests]
      , testGroup "stage 4 — computation" [computeTests]
      , testGroup "stage 5 — sequents & primitive rules" [ruleTests]
      , testGroup "stage 6 — tactics" [tacticTests]
      , testGroup "stage 7–9 — theories & examples" [exampleTests]
      ]
