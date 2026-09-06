-- | Interactive REPL. This is the principal IO boundary of nuprl-hs.
module Nuprl.REPL
  ( runREPL
  , evalLine
  , loadPath
  ) where

import Control.Monad.IO.Class (liftIO)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import System.Console.ANSI (hSupportsANSI, setSGRCode)
import System.Console.ANSI.Types
  ( Color (..)
  , ColorIntensity (..)
  , ConsoleIntensity (..)
  , ConsoleLayer (..)
  , SGR (..)
  )
import System.Console.Haskeline
import System.IO (stderr, stdout)

import Nuprl.Command
import Nuprl.Error
import Nuprl.Parse (parseTheoryAt)

-- | Load a theory file and install it in the session (IO).
loadPath :: FilePath -> Session -> IO (Session, [Output])
loadPath path sess = do
  txt <- TIO.readFile path
  case parseTheoryAt path txt of
    Left e -> pure (sess, [OutError e])
    Right thy -> pure (execCommand (CmdLoadTheory thy) sess)

-- | Interpret a single input line, performing any needed IO (currently just
-- @load@).
evalLine :: Session -> Text -> IO (Session, [Output])
evalLine sess line =
  let (w, rest) = splitFirst (T.strip line)
   in if w == "load"
        then
          if T.null rest
            then pure (sess, [OutError (ErrCommand "load requires a file path")])
            else loadPath (T.unpack rest) sess
        else
          case parseCommand (sessMode sess) line of
            Left e -> pure (sess, [OutError e])
            Right CmdQuit -> pure (sess, [OutQuit])
            Right cmd -> pure (execCommand cmd sess)

splitFirst :: Text -> (Text, Text)
splitFirst t =
  let (a, b) = T.break (== ' ') t
   in (a, T.strip b)

-- | Run an interactive session until the user quits.
runREPL :: Session -> IO ()
runREPL sess0 = do
  colour <- hSupportsANSI stdout
  putStrLn "nuprl-hs  (type `help` for commands, `quit` to exit)"
  runInputT settings (loop colour sess0)
  where
    settings =
      Settings
        { complete = completeSession
        , historyFile = Just ".nuprl_history"
        , autoAddHistory = True
        }

    loop colour sess = do
      minput <- getInputLine (prompt colour sess)
      case minput of
        Nothing -> liftIO (putStrLn "bye.")
        Just s -> do
          (sess', outs) <- liftIO (evalLine sess (T.pack s))
          liftIO (mapM_ (printOut colour) outs)
          if any isQuit outs
            then pure ()
            else loop colour sess'

    isQuit OutQuit = True
    isQuit _ = False

prompt :: Bool -> Session -> String
prompt colour sess =
  let base = case sessMode sess of
        TopLevel -> "nuprl> "
        InProof ps -> T.unpack ("prove:" <> psName ps <> "> ")
   in if colour
        then setSGRCode [SetColor Foreground Dull Cyan, SetConsoleIntensity BoldIntensity] <> base <> setSGRCode [Reset]
        else base

printOut :: Bool -> Output -> IO ()
printOut colour = \case
  OutInfo t -> TIO.putStrLn t
  OutQuit -> putStrLn "bye."
  OutError e -> do
    let msg = prettyError e
    if colour
      then TIO.hPutStrLn stderr (T.pack (setSGRCode [SetColor Foreground Vivid Red]) <> msg <> T.pack (setSGRCode [Reset]))
      else TIO.hPutStrLn stderr msg

completeSession :: CompletionFunc IO
completeSession = completeWord Nothing " \t" $ \w ->
  let cmds =
        [ "help"
        , "quit"
        , "load"
        , "list"
        , "show"
        , "check"
        , "prove"
        , "extract"
        , "eval"
        , "compute"
        , "dump"
        , "intro"
        , "elim"
        , "hyp"
        , "auto"
        , "eq"
        , "left"
        , "right"
        , "split"
        , "undo"
        , "abort"
        , "qed"
        , "goals"
        ]
      hits = filter (T.pack w `T.isPrefixOf`) (map T.pack cmds)
   in pure [simpleCompletion (T.unpack h) | h <- hits]
