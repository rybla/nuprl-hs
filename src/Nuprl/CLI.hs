-- | Command-line interface for nuprl-hs.
--
-- @nuprl@ with no arguments starts the REPL. Subcommands cover batch checking,
-- extraction, evaluation, and one-shot proof replay.
module Nuprl.CLI
  ( cliMain
  , Options (..)
  , CommandLine (..)
  , parseOptions
  ) where

import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Options.Applicative
import System.Exit (exitFailure, exitSuccess)
import System.IO (stderr)

import Nuprl.Command
import Nuprl.Compute (normalize)
import Nuprl.Error
import Nuprl.Library
import Nuprl.Parse (parseTerm)
import Nuprl.Pretty (renderTerm)
import Nuprl.REPL (loadPath, runREPL)
import Nuprl.Term (Term, uniformTerm)

-- | Parsed command line.
data Options = Options
  { optCommand :: CommandLine
  }
  deriving stock (Show)

data CommandLine
  = CmdREPL
  | CmdCheckFiles [FilePath]
  | CmdListFiles [FilePath]
  | CmdShowObj FilePath Text
  | CmdExtractObj FilePath Text
  | CmdEvalTerm Text
  | CmdComputeTerm Text
  | CmdDumpTerm Text
  | CmdHelpTopic (Maybe Text)
  deriving stock (Show)

parseOptions :: Parser Options
parseOptions =
  Options
    <$> (subparser commands <|> pure CmdREPL)
  where
    commands =
      mconcat
        [ command "repl" (info (pure CmdREPL) (progDesc "Start the interactive REPL"))
        , command
            "check"
            ( info
                (CmdCheckFiles <$> some (argument str (metavar "FILE")))
                (progDesc "Load and check theory files")
            )
        , command
            "list"
            ( info
                (CmdListFiles <$> many (argument str (metavar "FILE")))
                (progDesc "List library objects (after loading FILEs)")
            )
        , command
            "show"
            ( info
                (CmdShowObj <$> argument str (metavar "FILE") <*> (T.pack <$> argument str (metavar "NAME")))
                (progDesc "Show a named object from FILE")
            )
        , command
            "extract"
            ( info
                (CmdExtractObj <$> argument str (metavar "FILE") <*> (T.pack <$> argument str (metavar "NAME")))
                (progDesc "Print the extract of a theorem")
            )
        , command
            "eval"
            ( info
                (CmdEvalTerm . T.pack <$> argument str (metavar "TERM"))
                (progDesc "Pretty-print a term")
            )
        , command
            "compute"
            ( info
                (CmdComputeTerm . T.pack <$> argument str (metavar "TERM"))
                (progDesc "Normalize a term")
            )
        , command
            "dump"
            ( info
                (CmdDumpTerm . T.pack <$> argument str (metavar "TERM"))
                (progDesc "Print a term in uniform syntax")
            )
        , command
            "help"
            ( info
                (CmdHelpTopic <$> optional (T.pack <$> argument str (metavar "TOPIC")))
                (progDesc "Show help")
            )
        ]

optsInfo :: ParserInfo Options
optsInfo =
  info
    (parseOptions <**> helper)
    ( fullDesc
        <> header "nuprl — a NuPRL computational type theory prover"
        <> progDesc "Prove theorems in computational type theory. Run with no arguments for the REPL."
    )

-- | Program entry point.
cliMain :: IO ()
cliMain = do
  Options cmd <- execParser optsInfo
  run cmd

run :: CommandLine -> IO ()
run CmdREPL = runREPL emptySession
run (CmdHelpTopic m) = TIO.putStrLn (maybe helpText helpTopic m)
run (CmdEvalTerm t) = termAct renderTerm t
run (CmdComputeTerm t) = termAct (renderTerm . normalize) t
run (CmdDumpTerm t) = termAct uniformTerm t
run (CmdCheckFiles files) = do
  sess <- loadMany files emptySession
  case sess of
    Left e -> die e
    Right s -> do
      TIO.putStrLn (prettyLibrary (sessLibrary s))
      TIO.putStrLn "all theories checked."
run (CmdListFiles files) = do
  sess <- loadMany files emptySession
  case sess of
    Left e -> die e
    Right s -> TIO.putStrLn (prettyLibrary (sessLibrary s))
run (CmdShowObj file name) = do
  sess <- loadMany [file] emptySession
  case sess of
    Left e -> die e
    Right s ->
      let (s', outs) = execCommand (CmdShow name) s
       in mapM_ emit outs >> seq s' (pure ())
run (CmdExtractObj file name) = do
  sess <- loadMany [file] emptySession
  case sess of
    Left e -> die e
    Right s ->
      let (s', outs) = execCommand (CmdExtract name) s
       in mapM_ emit outs >> seq s' (pure ())

loadMany :: [FilePath] -> Session -> IO (Either NuprlError Session)
loadMany [] sess = pure (Right sess)
loadMany (f : fs) sess = do
  (sess', outs) <- loadPath f sess
  case [e | OutError e <- outs] of
    e : _ -> pure (Left e)
    [] -> loadMany fs sess'

termAct :: (Term -> Text) -> Text -> IO ()
termAct f t =
  case parseTerm t of
    Left e -> die e
    Right tm -> TIO.putStrLn (f tm)

die :: NuprlError -> IO ()
die e = do
  TIO.hPutStrLn stderr (prettyError e)
  exitFailure

emit :: Output -> IO ()
emit = \case
  OutInfo t -> TIO.putStrLn t
  OutError e -> die e
  OutQuit -> exitSuccess
