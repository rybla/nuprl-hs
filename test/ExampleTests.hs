module ExampleTests (exampleTests) where

import Data.Text.IO qualified as TIO
import System.Directory (doesDirectoryExist, doesFileExist)
import Test.Tasty
import Test.Tasty.HUnit

import Nuprl.Check
import Nuprl.Error
import Nuprl.Library
import Nuprl.Parse

exampleTests :: TestTree
exampleTests =
  testGroup
    "Examples"
    [ testCase "parse and check every examples/*.nuprl file" $ do
        exists <- doesDirectoryExist "examples"
        if not exists
          then assertFailure "examples/ directory is missing (run tests from the project root)"
          else do
            let files =
                  [ "examples/core.nuprl"
                  , "examples/functions.nuprl"
                  , "examples/logic.nuprl"
                  , "examples/equality.nuprl"
                  , "examples/integers.nuprl"
                  , "examples/lists.nuprl"
                  , "examples/classical.nuprl"
                  , "examples/cardinality.nuprl"
                  , "examples/denotational.nuprl"
                  , "examples/intersection.nuprl"
                  , "examples/sets.nuprl"
                  , "examples/quotients.nuprl"
                  , "examples/choice.nuprl"
                  , "examples/cps.nuprl"
                  , "examples/existence.nuprl"
                  , "examples/nd.nuprl"
                  , "examples/listprog.nuprl"
                  , "examples/combinatory.nuprl"
                  , "examples/hoare.nuprl"
                  , "examples/regular.nuprl"
                  , "examples/euclid.nuprl"
                  ]
            mapM_ checkFile files
    ]

checkFile :: FilePath -> Assertion
checkFile path = do
  present <- doesFileExist path
  if not present
    then assertFailure ("missing example file " <> path)
    else do
      txt <- TIO.readFile path
      case parseTheoryAt path txt of
        Left e -> assertFailure (path <> ": " <> show (prettyError e))
        Right thy ->
          case checkTheory coreLibrary thy of
            Left e -> assertFailure (path <> ": " <> show (prettyError e))
            Right _ -> pure ()
