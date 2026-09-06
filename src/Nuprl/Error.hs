-- | Error types used throughout the NuPRL implementation.
--
-- All kernel operations report failure via 'NuprlError' (or a more specific
-- type that can be injected into it). IO is confined to the CLI\/REPL; the
-- prover itself is a pure function @Library -> ... -> Either NuprlError a@.
module Nuprl.Error
  ( NuprlError (..)
  , RefineError (..)
  , TacticFail (..)
  , prettyError
  ) where

import Data.Text (Text)
import Data.Text qualified as T

-- | Top-level error for the NuPRL system.
data NuprlError
  = -- | Syntax error (parser). The payload is already pretty-printed.
    ErrParse Text
  | -- | A primitive refinement rule did not apply.
    ErrRefine RefineError
  | -- | A tactic failed.
    ErrTactic TacticFail
  | -- | Library \/ theory management error.
    ErrLibrary Text
  | -- | A theory failed to check.
    ErrCheck Text
  | -- | A REPL \/ CLI command could not be executed.
    ErrCommand Text
  deriving stock (Eq, Show)

-- | Why a primitive rule refused to apply.
data RefineError = RefineError
  { reRule :: Text
  , reReason :: Text
  }
  deriving stock (Eq, Show)

-- | Why a tactic failed. Tactics are expected to fail often (backtracking);
-- the message is for the user when the failure is uncaught.
data TacticFail = TacticFail
  { tfTactic :: Text
  , tfReason :: Text
  }
  deriving stock (Eq, Show)

-- | Render an error for the CLI.
prettyError :: NuprlError -> Text
prettyError = \case
  ErrParse msg -> "parse error:\n" <> msg
  ErrRefine (RefineError rule reason) ->
    "refinement error (" <> rule <> "): " <> reason
  ErrTactic (TacticFail tac reason) ->
    "tactic " <> tac <> " failed: " <> reason
  ErrLibrary msg -> "library error: " <> msg
  ErrCheck msg -> "check error: " <> msg
  ErrCommand msg -> "command error: " <> msg

instance Semigroup NuprlError where
  a <> _ = a

instance Monoid NuprlError where
  mempty = ErrCommand (T.pack "unknown error")
