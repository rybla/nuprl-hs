-- | Pure command processor for the NuPRL CLI and REPL.
--
-- IO (reading files, printing) lives in "Nuprl.REPL" and "Nuprl.CLI". This
-- module interprets commands against an in-memory 'Session'.
module Nuprl.Command
  ( Session (..)
  , emptySession
  , Mode (..)
  , ProofSession (..)
  , Command (..)
  , Output (..)
  , renderOutput
  , parseCommand
  , execCommand
  , helpText
  , helpTopic
  ) where

import Data.Char (isSpace)
import Data.Text (Text)
import Data.Text qualified as T

import Nuprl.Check
import Nuprl.Compute (normalize)
import Nuprl.Error
import Nuprl.Library
import Nuprl.Parse
import Nuprl.Pretty (renderTerm)
import Nuprl.Proof
import Nuprl.Sequent
import Nuprl.Tactic
import Nuprl.Term

-- | Top-level vs. interactive-proof mode.
data Mode
  = TopLevel
  | InProof ProofSession
  deriving stock (Show)

-- | State of an interactive proof.
data ProofSession = ProofSession
  { psName :: Name
  , psProof :: Proof
  , psUndo :: [(Proof, [TacticExpr])]
  , psScript :: [TacticExpr]
  }
  deriving stock (Show)

-- | The full REPL state.
data Session = Session
  { sessLibrary :: Library
  , sessMode :: Mode
  }
  deriving stock (Show)

emptySession :: Session
emptySession = Session coreLibrary TopLevel

-- | User-facing commands. File IO is represented by 'CmdLoadText' (the REPL
-- reads the file and passes the contents).
data Command
  = CmdHelp (Maybe Text)
  | CmdQuit
  | CmdLoadTheory Theory
  | CmdList
  | CmdShow Name
  | CmdCheck (Maybe Name)
  | CmdProve Name
  | CmdExtract Name
  | CmdEval Term
  | CmdCompute Term
  | CmdDump Term
  | CmdTactic TacticExpr
  | CmdGoals
  | CmdUndo
  | CmdAbort
  | CmdQed
  | CmdStatus
  deriving stock (Show)

-- | A message produced by a command.
data Output
  = OutInfo Text
  | OutError NuprlError
  | OutQuit
  deriving stock (Show)

renderOutput :: Output -> Text
renderOutput = \case
  OutInfo t -> t
  OutError e -> prettyError e
  OutQuit -> "bye."

--------------------------------------------------------------------------------
-- Parsing commands
--------------------------------------------------------------------------------

parseCommand :: Mode -> Text -> Either NuprlError Command
parseCommand mode raw =
  let line = T.strip raw
   in if T.null line
        then Left (ErrCommand "empty command")
        else
          let (w, rest) = splitWord line
           in parseCmd mode w (T.strip rest) line

splitWord :: Text -> (Text, Text)
splitWord t =
  let (a, b) = T.break isSpace t
   in (a, T.stripStart b)

parseCmd :: Mode -> Text -> Text -> Text -> Either NuprlError Command
parseCmd mode w rest whole =
  case w of
    "help" -> Right (CmdHelp (if T.null rest then Nothing else Just rest))
    "?" -> Right (CmdHelp (if T.null rest then Nothing else Just rest))
    "quit" -> Right CmdQuit
    "exit" -> Right CmdQuit
    ":q" -> Right CmdQuit
    "list" -> Right CmdList
    "ls" -> Right CmdList
    "status" -> Right CmdStatus
    "goals" -> Right CmdGoals
    "undo" -> Right CmdUndo
    "abort" -> Right CmdAbort
    "qed" -> Right CmdQed
    "show" -> named CmdShow rest
    "prove" -> named CmdProve rest
    "extract" -> named CmdExtract rest
    "check" ->
      Right (CmdCheck (if T.null rest then Nothing else Just rest))
    "eval" -> termCmd CmdEval rest
    "compute" -> termCmd CmdCompute rest
    "dump" -> termCmd CmdDump rest
    "load" -> Left (ErrCommand "load: use the REPL/CLI to read a file path")
    _ ->
      case mode of
        InProof {} ->
          case parseTactic whole of
            Right tx -> Right (CmdTactic tx)
            Left e -> Left e
        TopLevel ->
          Left (ErrCommand ("unknown command '" <> w <> "'; try `help`"))
  where
    named cons t
      | T.null t = Left (ErrCommand (w <> " requires a name"))
      | otherwise = Right (cons t)
    termCmd cons t
      | T.null t = Left (ErrCommand (w <> " requires a term"))
      | otherwise = cons <$> parseTerm t

--------------------------------------------------------------------------------
-- Execution
--------------------------------------------------------------------------------

execCommand :: Command -> Session -> (Session, [Output])
execCommand cmd sess = case cmd of
  CmdHelp m -> (sess, [OutInfo (maybe helpText helpTopic m)])
  CmdQuit -> (sess, [OutQuit])
  CmdLoadTheory thy ->
    case checkTheory (sessLibrary sess) thy of
      Left e -> (sess, [OutError e])
      Right lib ->
        ( sess {sessLibrary = lib}
        , [OutInfo ("loaded theory " <> theoryName thy)]
        )
  CmdList ->
    (sess, [OutInfo (prettyLibrary (sessLibrary sess))])
  CmdShow name ->
    (sess, [OutInfo (showObject (sessLibrary sess) name)])
  CmdCheck Nothing ->
    case checkLibrary (sessLibrary sess) of
      Left e -> (sess, [OutError e])
      Right lib ->
        ( sess {sessLibrary = lib}
        , [OutInfo "library checked."]
        )
  CmdCheck (Just name) ->
    case lookupObject name (sessLibrary sess) of
      Just (ObjTheorem th) ->
        case checkTheorem (sessLibrary sess) name th of
          Left e -> (sess, [OutError e])
          Right th' ->
            ( sess {sessLibrary = insertObject name (ObjTheorem th') (sessLibrary sess)}
            , [OutInfo ("theorem " <> name <> " is complete.")]
            )
      Just _ -> (sess, [OutInfo (name <> " has no proof to check.")])
      Nothing -> (sess, [OutError (ErrLibrary ("unknown object " <> name))])
  CmdProve name -> startProve name sess
  CmdExtract name ->
    case lookupObject name (sessLibrary sess) of
      Just (ObjTheorem th)
        | Just e <- thmExtract th ->
            (sess, [OutInfo (renderTerm e)])
        | otherwise ->
            case prove (sessLibrary sess) (thmGoal th) (thmScript th) of
              Left e -> (sess, [OutError e])
              Right extr -> (sess, [OutInfo (renderTerm extr)])
      _ -> (sess, [OutError (ErrLibrary ("no theorem " <> name))])
  CmdEval t ->
    (sess, [OutInfo (renderTerm t)])
  CmdCompute t ->
    (sess, [OutInfo (renderTerm (normalize t))])
  CmdDump t ->
    (sess, [OutInfo (uniformTerm t)])
  CmdTactic tx -> applyTx tx sess
  CmdGoals ->
    case sessMode sess of
      InProof ps -> (sess, [OutInfo (prettyProof (psProof ps))])
      TopLevel -> (sess, [OutError (ErrCommand "not in a proof")])
  CmdUndo ->
    case sessMode sess of
      InProof ps@ProofSession {psUndo = (u, scr) : us} ->
        let ps' = ps {psProof = u, psUndo = us, psScript = scr}
         in (sess {sessMode = InProof ps'}, [OutInfo "undone.", OutInfo (focusView ps')])
      InProof _ -> (sess, [OutError (ErrCommand "nothing to undo")])
      TopLevel -> (sess, [OutError (ErrCommand "not in a proof")])
  CmdAbort ->
    (sess {sessMode = TopLevel}, [OutInfo "proof aborted."])
  CmdQed ->
    case sessMode sess of
      InProof ps
        | isComplete (psProof ps) ->
            case extractProof (psProof ps) of
              Left e -> (sess, [OutError (ErrRefine e)])
              Right extr ->
                let th =
                      Theorem
                        { thmGoal = seqConcl (proofGoal (psProof ps))
                        , thmScript = TxSeq (reverse (psScript ps))
                        , thmStatus = StatusComplete
                        , thmExtract = Just extr
                        }
                    lib = insertObject (psName ps) (ObjTheorem th) (sessLibrary sess)
                 in ( Session lib TopLevel
                    , [OutInfo ("qed. extract: " <> renderTerm extr)]
                    )
        | otherwise ->
            ( sess
            , [OutError (ErrCommand ("proof incomplete (" <> T.pack (show (openCount (psProof ps))) <> " open goals)"))]
            )
      TopLevel -> (sess, [OutError (ErrCommand "not in a proof")])
  CmdStatus ->
    (sess, [OutInfo (statusLine sess)])

startProve :: Name -> Session -> (Session, [Output])
startProve name sess =
  case lookupObject name (sessLibrary sess) of
    Just (ObjTheorem th) ->
      let p = Unrefined (emptySequent (thmGoal th))
          ps = ProofSession name p [] []
       in ( sess {sessMode = InProof ps}
          , [OutInfo ("proving " <> name), OutInfo (focusView ps)]
          )
    Nothing ->
      -- Allow `prove <term>`? No: require a theorem. Users can `theorem` in files.
      (sess, [OutError (ErrLibrary ("unknown theorem " <> name))])
    _ -> (sess, [OutError (ErrLibrary (name <> " is not a theorem"))])

applyTx :: TacticExpr -> Session -> (Session, [Output])
applyTx tx sess =
  case sessMode sess of
    TopLevel -> (sess, [OutError (ErrCommand "not in a proof (use `prove <name>`)")])
    InProof ps ->
      let env = lemmaEnv (sessLibrary sess)
       in case applyTactic env (evalTactic tx) (psProof ps) of
            Left tf -> (sess, [OutError (ErrTactic tf), OutInfo (focusView ps)])
            Right p' ->
              let ps' =
                    ps
                      { psProof = p'
                      , psUndo = (psProof ps, psScript ps) : psUndo ps
                      , psScript = tx : psScript ps
                      }
                  done =
                    if isComplete p'
                      then "\nProof complete. Type `qed` to save."
                      else ""
               in ( sess {sessMode = InProof ps'}
                  , [OutInfo (focusView ps' <> done)]
                  )

focusView :: ProofSession -> Text
focusView ps =
  case openGoals (psProof ps) of
    [] -> prettyProof (psProof ps)
    (addr, sq) : rest ->
      "goal "
        <> T.pack (show (1 :: Int))
        <> " of "
        <> T.pack (show (1 + length rest))
        <> "\n"
        <> prettySequent sq
        <> "\n(addr "
        <> prettyAddr addr
        <> ")"
  where
    prettyAddr (Addr xs) = T.intercalate "." (map (T.pack . show) xs)

showObject :: Library -> Name -> Text
showObject lib name =
  case lookupObject name lib of
    Nothing -> "unknown object " <> name
    Just (ObjTheorem th) ->
      "theorem "
        <> name
        <> " :\n  "
        <> renderTerm (thmGoal th)
        <> "\nproof\n  "
        <> prettyTacticExpr (thmScript th)
        <> "\nqed"
        <> maybe "" (\e -> "\nextract: " <> renderTerm e) (thmExtract th)
    Just (ObjAbs a) ->
      "abs "
        <> opIdText (absOpId a)
        <> " == "
        <> renderTerm (absRhs a)
        <> if absSoft a then "\n(soft)" else ""
    Just (ObjComment t) -> "comment: " <> t
    Just (ObjSoft ns) -> "soft " <> T.intercalate ", " ns

statusLine :: Session -> Text
statusLine sess =
  let n = length (libOrder (sessLibrary sess))
      mode = case sessMode sess of
        TopLevel -> "top-level"
        InProof ps -> "proving " <> psName ps
   in "objects: " <> T.pack (show n) <> "; mode: " <> mode

--------------------------------------------------------------------------------
-- Help
--------------------------------------------------------------------------------

helpText :: Text
helpText =
  T.unlines
    [ "nuprl-hs — a modern NuPRL computational type theory prover"
    , ""
    , "Top-level commands:"
    , "  help [topic]       this help, or a topic (tactics, terms, rules, examples)"
    , "  load FILE          load and check a .nuprl theory file"
    , "  list               list library objects"
    , "  show NAME          show a library object"
    , "  check [NAME]       recheck a theorem, or the whole library"
    , "  prove NAME         enter interactive proof mode"
    , "  extract NAME       print the extract of a complete theorem"
    , "  eval TERM          pretty-print a term"
    , "  compute TERM       reduce a term to normal form"
    , "  dump TERM          print a term in uniform syntax"
    , "  quit               exit"
    , ""
    , "Proof-mode commands:"
    , "  intro [x|left|right|with TERM]"
    , "  elim N [with TERM]  hyp [N]   auto   eq   compute"
    , "  left  right  split  exists TERM  arith  prove_prop"
    , "  D [N]  lemma NAME  cut TERM  thin N"
    , "  THEN / ORELSE / REPEAT / TRY / THENL"
    , "  goals   undo   abort   qed"
    , ""
    , "Type `help tactics`, `help terms`, or `help rules` for more."
    ]

helpTopic :: Text -> Text
helpTopic t = case T.toLower t of
  "tactics" -> helpTactics
  "terms" -> helpTerms
  "rules" -> helpRules
  "examples" -> helpExamples
  _ -> "unknown help topic '" <> t <> "'. Try tactics, terms, rules, examples."

helpTactics :: Text
helpTactics =
  T.unlines
    [ "Tactic language"
    , "  intro            inhabit the conclusion (λ, pair, Ax, …)"
    , "  intro x          name the bound variable"
    , "  intro left/right disjoint union"
    , "  intro with t     witness for ∃ / Σ / set"
    , "  elim N           eliminate hypothesis N"
    , "  elim N with t    instantiate a Π / ∀ / ⋂ hypothesis"
    , "  hyp [N]          use a hypothesis (or search)"
    , "  auto             bounded automated proof search"
    , "  eq               canonical equality / membership"
    , "  arith            closed integer equalities"
    , "  D [N]            decompose clause N (0 = conclusion)"
    , "  decide a = b     case analysis on integer equality"
    , "  decide a < b     case analysis on integer comparison"
    , "  decide t         case analysis on a union-typed term"
    , "  t1 THEN t2       run t2 on every new subgoal"
    , "  t1 ORELSE t2     backtracking"
    , "  REPEAT t         apply until failure"
    , "  TRY t            t ORELSE idtac"
    ]

helpTerms :: Text
helpTerms =
  T.unlines
    [ "Term syntax (ASCII and Unicode)"
    , "  U{i}  P{i}  Void  Unit  Int  Atom  True  False  Ax"
    , "  λx. t            (x:A) → B        A → B"
    , "  <a, b>           (x:A) × B        A × B"
    , "  inl t | inr t    A ⊎ B            A ∨ B"
    , "  a = b ∈ A        a ∈ A            ¬A"
    , "  ∀x:A. B          ∃x:A. B          A ⇒ B"
    , "  {x:A | P}        [A]   (squash)   List A"
    , "  ⋂x:A. B          A ∩ B  (cap)     isect(A; x.B)"
    , "  (x,y):A // E     A // E           quotient(A; x,y.E)"
    , "  a < b            a ≤ b            n % m        -n"
    , "  ind(n; …)        n :: ns          [a, b] lists / [T] squash"
    ]

helpRules :: Text
helpRules =
  T.unlines
    [ "Primitive refinement rules (the kernel)"
    , "  hyp N              use hypothesis N"
    , "  intro              type-directed introduction"
    , "  elim N             type-directed elimination"
    , "  eq                 canonical equality"
    , "  compute            weak-head reduce the conclusion"
    , "  cut T as x         assert T"
    , "  lemma NAME         add a complete theorem as a hypothesis"
    , "  thin N             drop a hypothesis"
    , ""
    , "All completed proofs are trees of these rules. Tactics search for such trees."
    ]

helpExamples :: Text
helpExamples =
  T.unlines
    [ "Example theories live in the examples/ directory:"
    , "  examples/core.nuprl         logic encodings"
    , "  examples/functions.nuprl    combinators, products, coproducts"
    , "  examples/logic.nuprl        intuitionistic logic, squash"
    , "  examples/equality.nuprl     equality, atoms, congruence"
    , "  examples/integers.nuprl     arithmetic, comparison, induction"
    , "  examples/lists.nuprl        lists, recursor, append"
    , "  examples/classical.nuprl    DNE from excluded middle"
    , "  examples/cardinality.nuprl  equipollence and pigeonhole"
    , "  examples/denotational.nuprl streams of states, program meaning"
    , "  examples/intersection.nuprl family intersection (isect)"
    , "  examples/sets.nuprl         set types, Nat, Positive, Bool"
    , "  examples/quotients.nuprl    quotient types, integers mod 2"
    , "  examples/choice.nuprl       constructive axiom of choice"
    , "  examples/cps.nuprl          CPS as double-negation translation"
    , "  examples/existence.nuprl    strong vs weak existence"
    , "  examples/nd.nuprl           depth-indexed ND, soundness"
    , "  examples/listprog.nuprl     lists as a programming theory"
    , "  examples/combinatory.nuprl  SKI and Church encodings"
    , "  examples/hoare.nuprl        Hoare logic on streams of states"
    , "  examples/regular.nuprl      regular sets / Kleene algebra"
    , "  examples/euclid.nuprl       verified Euclidean algorithm"
    , ""
    , "Load one with:  nuprl check examples/logic.nuprl"
    ]
