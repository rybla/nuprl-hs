-- | Pre-process a theory the same way the CLI does: parse, check, extract,
-- compute, dump. The results are embedded in HTML; the browser does no proving.
module Analyze
  ( ExampleMeta (..)
  , AnnotatedExample (..)
  , AnnotatedItem (..)
  , AnnotatedTheorem (..)
  , ProofStats (..)
  , exampleMetas
  , lookupMeta
  , headerComment
  , annotateSource
  , lookupAbs
  , unfoldAny
  , termSize
  , shorten
  , proofStats
  , explainRule
  , explainTactic
  , explainTerm
  , termKind
  , Kind (..)
  , kindClass
  , kindLabel
  ) where

import Data.List (sortOn)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T

import Nuprl.Check (checkTheorem, proveExpr)
import Nuprl.Compute (unfoldSoftOnce)
import Nuprl.Error (prettyError)
import Nuprl.Library
import Nuprl.Parse (parseTheoryAt)
import Nuprl.Pretty (renderTerm)
import Nuprl.Proof
import Nuprl.Subst (alphaEq, occursFree)
import Nuprl.Tactic (IntroArgExpr (..), TacticExpr (..), prettyTacticExpr)
import Nuprl.Term

-- | Curated copy for the landing page and example headers.
data ExampleMeta = ExampleMeta
  { emSlug :: Text
  , emTitle :: Text
  , emTagline :: Text
  , emSection :: Maybe Text
  }
  deriving stock (Eq, Show)

exampleMetas :: [ExampleMeta]
exampleMetas =
  [ ExampleMeta "core" "Core" "Logic encodings as named abstractions; True is Unit." Nothing
  , ExampleMeta "functions" "Functions" "Category of types and functions: composition laws, Fork/Case universal properties, currying isomorphism, extensionality." Nothing
  , ExampleMeta "logic" "Logic" "Intuitionistic predicate logic, De Morgan, quantifiers, and squash." Nothing
  , ExampleMeta "equality" "Equality" "Reflexivity, symmetry, transitivity, Leibniz substitution, constructor congruences, and discrimination." Nothing
  , ExampleMeta "integers" "Integers" "Discrete decidability, strict order decidability, sign splitting, and ternary integer induction." Nothing
  , ExampleMeta "lists" "Lists" "Foundational list theory: constructors, discrimination, structural recursion, Map, Append, Length, and reduction equations." Nothing
  , ExampleMeta "classical" "Classical" "DNE and stability recovered from excluded middle." Nothing
  , ExampleMeta
      "cardinality"
      "Cardinality"
      "Equipollence, finite segments, and the pigeonhole principle."
      (Just "Constable et al. §11.3")
  , ExampleMeta
      "denotational"
      "Denotational semantics"
      "Stream-of-states model, semantic equivalence (SemEq), algebraic command laws, and depth-indexed program syntax."
      (Just "Constable et al. §11.6")
  , ExampleMeta
      "intersection"
      "Intersection"
      "Family intersection ⋂x:A. B and independent A ∩ B. The extract ignores the index."
      Nothing
  , ExampleMeta
      "sets"
      "Sets"
      "Set types {x:A | P}: comprehension, subset preorder, empty/full/singleton, Nat, Positive, Bool."
      Nothing
  , ExampleMeta
      "quotients"
      "Quotients"
      "Quotient types (x,y):A // E, the functionality principle, well-definedness, and counterexamples."
      (Just "Constable et al. §10.3")
  , ExampleMeta
      "choice"
      "Axiom of choice"
      "Type-theoretic AC is a theorem: a total relation yields a choice function."
      Nothing
  , ExampleMeta
      "cps"
      "CPS / double negation"
      "Continuation monad, algebraic laws, Kleisli composition, and constructive double-negation embedding."
      Nothing
  , ExampleMeta
      "existence"
      "Weak vs. strong existence"
      "Σ vs. squash vs. ¬¬∃; the witness is in the extract only for strong existence."
      Nothing
  , ExampleMeta
      "nd"
      "Natural deduction"
      "Depth-indexed object logic, formula validity under all valuations, and soundness of natural deduction."
      Nothing
  , ExampleMeta
      "listprog"
      "Lists as programs"
      "List programming, symbol tables / environments (EmptyEnv, Extend, Lookup), and higher-order combinators (Foldr, Filter)."
      (Just "Constable et al. §11.2")
  , ExampleMeta
      "combinatory"
      "Combinatory logic"
      "SKI, B, CFlip, W combinator algebra, typing and reduction laws, and polymorphic Church encodings."
      Nothing
  , ExampleMeta
      "hoare"
      "Hoare logic"
      "Sound structural rules of Hoare logic (Skip, Pre, Post, Conjunction, Disjunction, Assignment) over stream semantics."
      (Just "Constable et al. §11.6")
  , ExampleMeta
      "regular"
      "Regular sets"
      "Regular expressions as languages over words, language containment preorder, mutual equivalence, and Kleene algebra."
      (Just "Constable et al. §11.4")
  , ExampleMeta
      "euclid"
      "Euclidean algorithm"
      "Verified Euclidean algorithm, structural step properties, common divisor specification, and coprimality."
      Nothing
  ]

lookupMeta :: Text -> Maybe ExampleMeta
lookupMeta slug = case filter (\m -> emSlug m == slug) exampleMetas of
  m : _ -> Just m
  [] -> Nothing

data AnnotatedExample = AnnotatedExample
  { axPath :: FilePath
  , axSlug :: Text
  , axSource :: Text
  , axHeader :: Text
  , axTheory :: Theory
  , axLibrary :: Library
  , axItems :: [AnnotatedItem]
  , axError :: Maybe Text
  }
  deriving stock (Show)

data AnnotatedItem
  = ItemComment Name Text
  | ItemAbs Abstraction
  | ItemSoft [Name]
  | ItemTheorem AnnotatedTheorem
  deriving stock (Show)

data AnnotatedTheorem = AnnotatedTheorem
  { athName :: Name
  , athGoal :: Term
  , athScript :: TacticExpr
  , athExtract :: Maybe Term
  , athProof :: Maybe Proof
  , athStats :: ProofStats
  , athError :: Maybe Text
  }
  deriving stock (Show)

data ProofStats = ProofStats
  { psNodes :: Int
  , psOpen :: Int
  , psRules :: [(Text, Int)]
  , psLemmas :: [Name]
  }
  deriving stock (Eq, Show)

emptyStats :: ProofStats
emptyStats = ProofStats 0 0 [] []

-- | Parse and check a theory file, replaying each tactic script so the proof
-- tree is available for the explorer (the CLI's @check@ / @extract@ / @show@).
annotateSource :: FilePath -> Text -> AnnotatedExample
annotateSource path src =
  let slug = T.pack (takeBase path)
      hdr = headerComment src
   in case parseTheoryAt path src of
        Left e ->
          AnnotatedExample
            { axPath = path
            , axSlug = slug
            , axSource = src
            , axHeader = hdr
            , axTheory = Theory slug [] []
            , axLibrary = coreLibrary
            , axItems = []
            , axError = Just (prettyError e)
            }
        Right thy ->
          let (lib, items, err) = checkAndAnnotate thy
           in AnnotatedExample
                { axPath = path
                , axSlug = slug
                , axSource = src
                , axHeader = hdr
                , axTheory = thy
                , axLibrary = lib
                , axItems = items
                , axError = err
                }

takeBase :: FilePath -> String
takeBase fp =
  let name = reverse . takeWhile (`notElem` ("/\\" :: String)) . reverse $ fp
   in case dropWhile (/= '.') (reverse name) of
        '.' : _ -> reverse (drop 1 (dropWhile (/= '.') (reverse name)))
        _ -> name

-- | Leading @--@ / @-- |@ commentary, before the @theory@ keyword.
headerComment :: Text -> Text
headerComment src =
  T.strip . T.unlines . dropWhile T.null . map stripDash $
    takeWhile isPreamble (T.lines src)
  where
    isPreamble l =
      let s = T.strip l
       in T.null s || T.isPrefixOf "--" s
    stripDash l =
      let s = T.strip l
       in if T.isPrefixOf "-- |" s
            then T.strip (T.drop 4 s)
            else
              if T.isPrefixOf "--" s
                then T.strip (T.drop 2 s)
                else s

checkAndAnnotate :: Theory -> (Library, [AnnotatedItem], Maybe Text)
checkAndAnnotate thy =
  case importTheory thy coreLibrary of
    Left e -> (coreLibrary, [], Just (prettyError e))
    Right lib0 -> go lib0 [] Nothing (theoryObjects thy)
  where
    go lib acc err [] = (lib, reverse acc, err)
    go lib acc err ((n, ObjComment t) : rest) =
      go lib (ItemComment n t : acc) err rest
    go lib acc err ((_, ObjSoft ns) : rest) =
      go (setSoft ns lib) (ItemSoft ns : acc) err rest
    go lib acc err ((n, ObjAbs a) : rest) =
      let a' = case lookupObject n lib of
            Just (ObjAbs b) -> b
            _ -> a
       in go lib (ItemAbs a' : acc) err rest
    go lib acc err ((n, ObjTheorem th) : rest) =
      case proveExpr lib (thmGoal th) (thmScript th) of
        Left e ->
          let ath =
                AnnotatedTheorem
                  { athName = n
                  , athGoal = thmGoal th
                  , athScript = thmScript th
                  , athExtract = Nothing
                  , athProof = Nothing
                  , athStats = emptyStats
                  , athError = Just (prettyError e)
                  }
              err' = Just $ maybe ("theorem " <> n <> " failed") (<> ("; " <> n)) err
           in go lib (ItemTheorem ath : acc) err' rest
        Right (prf, extr) ->
          case checkTheorem lib n th of
            Left e ->
              let ath =
                    AnnotatedTheorem
                      { athName = n
                      , athGoal = thmGoal th
                      , athScript = thmScript th
                      , athExtract = Just extr
                      , athProof = Just prf
                      , athStats = proofStats prf
                      , athError = Just (prettyError e)
                      }
               in go lib (ItemTheorem ath : acc) err rest
            Right th' ->
              let ath =
                    AnnotatedTheorem
                      { athName = n
                      , athGoal = thmGoal th
                      , athScript = thmScript th
                      , athExtract = Just extr
                      , athProof = Just prf
                      , athStats = proofStats prf
                      , athError = Nothing
                      }
                  lib' = insertObject n (ObjTheorem th') lib
               in go lib' (ItemTheorem ath : acc) err rest

--------------------------------------------------------------------------------
-- Proof statistics (from the refinement tree)
--------------------------------------------------------------------------------

proofStats :: Proof -> ProofStats
proofStats p =
  let names = proofRules p
      hist =
        sortOn (negate . snd) . Map.toList $
          Map.fromListWith (+) [(n, 1 :: Int) | n <- names]
      lemmas =
        [ T.strip rest
        | n <- names
        , Just rest <- [T.stripPrefix "lemma " n]
        , not (T.null (T.strip rest))
        ]
   in ProofStats
        { psNodes = length names
        , psOpen = openCount p
        , psRules = hist
        , psLemmas = lemmas
        }

proofRules :: Proof -> [Text]
proofRules (Unrefined _) = []
proofRules (Refined _ n cs _) = n : concatMap proofRules cs

--------------------------------------------------------------------------------
-- Library / computation helpers (CLI: dump, compute, eval)
--------------------------------------------------------------------------------

lookupAbs :: Library -> Text -> Maybe Abstraction
lookupAbs lib n =
  case lookupObject n lib of
    Just (ObjAbs a) -> Just a
    _ ->
      case [a | ObjAbs a <- Map.elems (libObjects lib), opIdText (absOpId a) == n] of
        a : _ -> Just a
        [] -> Nothing

-- | Unfold a user abstraction or a soft encoding at the root, if any.
unfoldAny :: Library -> Term -> Maybe Term
unfoldAny lib t =
  case unfoldAbs lib t of
    Just t' -> Just t'
    Nothing ->
      case t of
        TVar (Var n) ->
          case lookupAbs lib n of
            Just a | null (absFormals a) -> Just (absRhs a)
            _ -> unfoldSoftOnce t
        _ -> unfoldSoftOnce t

termSize :: Term -> Int
termSize (TVar _) = 1
termSize (TOp _ bts) = 1 + sum [termSize (btBody b) | b <- bts]

shorten :: Int -> Text -> Text
shorten n t
  | T.length t <= n = t
  | otherwise = T.take (n - 1) t <> "…"

--------------------------------------------------------------------------------
-- Semantic classification
--------------------------------------------------------------------------------

data Kind
  = KType
  | KBinder
  | KVar
  | KConn
  | KKw
  | KNum
  | KAbs
  | KVal
  | KTac
  | KExtract
  | KGoal
  | KComment
  | KKeyword
  | KPunct
  deriving stock (Eq, Show)

kindClass :: Kind -> Text
kindClass = \case
  KType -> "sem-type"
  KBinder -> "sem-binder"
  KVar -> "sem-var"
  KConn -> "sem-conn"
  KKw -> "sem-kw"
  KNum -> "sem-num"
  KAbs -> "sem-abs"
  KVal -> "sem-val"
  KTac -> "sem-tac"
  KExtract -> "sem-extract"
  KGoal -> "sem-goal"
  KComment -> "sem-comment"
  KKeyword -> "sem-keyword"
  KPunct -> "sem-punct"

kindLabel :: Kind -> Text
kindLabel = \case
  KType -> "type"
  KBinder -> "binder"
  KVar -> "variable"
  KConn -> "connective"
  KKw -> "constructor"
  KNum -> "numeral"
  KAbs -> "abstraction"
  KVal -> "value"
  KTac -> "tactic"
  KExtract -> "extract"
  KGoal -> "goal"
  KComment -> "comment"
  KKeyword -> "keyword"
  KPunct -> "punctuation"

termKind :: Library -> Term -> Kind
termKind lib t
  | isAbsName lib t = KAbs
  | isSoftLogic t = KConn
  | isCanonicalType t = KType
  | isCanonicalValue t = KVal
  | otherwise = case t of
      TVar _ -> KVar
      TNat _ -> KNum
      TLambda {} -> KVal
      TApply {} -> KVal
      TAdd {} -> KVal
      TSub {} -> KVal
      TMul {} -> KVal
      TDiv {} -> KVal
      TRem {} -> KVal
      TMinus {} -> KVal
      TLt {} -> KType
      TEqual {} -> KType
      TMember {} -> KType
      TAll {} -> KConn
      TExists {} -> KConn
      TNot {} -> KConn
      TAnd {} -> KConn
      TOr {} -> KConn
      TImplies {} -> KConn
      TIff {} -> KConn
      TOp {} -> KVal

isAbsName :: Library -> Term -> Bool
isAbsName lib = \case
  TVar (Var n) -> isJustAbs n
  TOp (Operator oid _) _ -> isJustAbs (opIdText oid)
  where
    isJustAbs n = case lookupAbs lib n of
      Just _ -> True
      Nothing -> False

--------------------------------------------------------------------------------
-- Explanations (precomputed into tooltips)
--------------------------------------------------------------------------------

explainTerm :: Library -> Term -> Text
explainTerm lib t = case t of
  TUniverse l ->
    "Universe of types at level " <> prettyLevel l <> ". Types inhabit a cumulative hierarchy U{i}."
  TProp l ->
    "Propositional universe P{" <> prettyLevel l <> "}, a soft encoding of U{" <> prettyLevel l <> "}."
  TVoid -> "The empty type. No canonical inhabitant; eliminating Void (ex falso) proves anything."
  TUnit -> "The unit type. Canonical inhabitant: Ax."
  TAxiom -> "The canonical inhabitant of Unit, of an equality, and of other axiomatically inhabited types."
  TInt -> "The type of integers."
  TAtom -> "The type of tokens (quoted strings)."
  TTrue -> "Soft encoding of Unit: the true proposition."
  TFalse -> "Soft encoding of Void: the false proposition."
  TNat n -> "Integer numeral " <> T.pack (show n) <> "."
  TToken s -> "Token " <> T.pack (show s) <> " ∈ Atom."
  TNil -> "The empty list."
  TLambda x b ->
    "A λ-abstraction binding "
      <> varText x
      <> " in "
      <> renderTerm b
      <> ". Canonical inhabitant of a function type (Π)."
  TAll a x b ->
    "Universal quantifier ∀"
      <> varText x
      <> ":"
      <> renderTerm a
      <> ". "
      <> renderTerm b
      <> ". Soft encoding of the dependent function type."
  TExists a x b ->
    "Existential quantifier ∃"
      <> varText x
      <> ":"
      <> renderTerm a
      <> ". "
      <> renderTerm b
      <> ". Soft encoding of the dependent pair type (Σ)."
  TNot a -> "Negation ¬(" <> renderTerm a <> "), the soft encoding of A → Void."
  TImplies a b ->
    "Implication "
      <> renderTerm a
      <> " ⇒ "
      <> renderTerm b
      <> ", the soft encoding of the function type A → B."
  TOr a b ->
    "Disjunction "
      <> renderTerm a
      <> " ∨ "
      <> renderTerm b
      <> ", the soft encoding of the disjoint union A ⊎ B."
  TAnd a b ->
    "Conjunction "
      <> renderTerm a
      <> " ∧ "
      <> renderTerm b
      <> ", the soft encoding of the product A × B."
  TIff a b ->
    "Biconditional "
      <> renderTerm a
      <> " ⇔ "
      <> renderTerm b
      <> ", i.e. (A → B) × (B → A)."
  TLt a b -> "Integer comparison " <> renderTerm a <> " < " <> renderTerm b <> ". Inhabited (by Ax) when the relation holds."
  TFunction a x b
    | isDummyVar x || not (occursFree x b) ->
        "Function type " <> renderTerm a <> " → " <> renderTerm b <> "."
    | otherwise ->
        "Dependent function type (Π): (" <> varText x <> ":" <> renderTerm a <> ") → " <> renderTerm b <> "."
  TProduct a x b
    | isDummyVar x || not (occursFree x b) ->
        "Product type " <> renderTerm a <> " × " <> renderTerm b <> "."
    | otherwise ->
        "Dependent pair type (Σ): (" <> varText x <> ":" <> renderTerm a <> ") × " <> renderTerm b <> "."
  TUnion a b ->
    "Disjoint union "
      <> renderTerm a
      <> " ⊎ "
      <> renderTerm b
      <> ". Canonical inhabitants: inl / inr."
  TEqual ty a b
    | alphaEq a b -> "Membership " <> renderTerm a <> " ∈ " <> renderTerm ty <> "."
    | otherwise -> "Equality " <> renderTerm a <> " = " <> renderTerm b <> " ∈ " <> renderTerm ty <> ". Inhabited by Ax when true."
  TMember tm ty -> "Membership " <> renderTerm tm <> " ∈ " <> renderTerm ty <> ", i.e. " <> renderTerm tm <> " = " <> renderTerm tm <> " ∈ " <> renderTerm ty <> "."
  TAdd a b -> "Integer addition " <> renderTerm a <> " + " <> renderTerm b <> "."
  TSub a b -> "Integer subtraction " <> renderTerm a <> " − " <> renderTerm b <> "."
  TMul a b -> "Integer multiplication " <> renderTerm a <> " · " <> renderTerm b <> "."
  TDiv a b -> "Integer division " <> renderTerm a <> " / " <> renderTerm b <> "."
  TRem a b -> "Integer remainder " <> renderTerm a <> " % " <> renderTerm b <> "."
  TMinus a -> "Integer negation −(" <> renderTerm a <> ")."
  TCons h tl -> "List cons " <> renderTerm h <> " :: " <> renderTerm tl <> "."
  TPair a b ->
    "A pair 〈"
      <> renderTerm a
      <> ", "
      <> renderTerm b
      <> "〉. Canonical inhabitant of a product / Σ / conjunction."
  TInl a -> "Left injection inl (" <> renderTerm a <> ") of a disjoint union (or ∨)."
  TInr a -> "Right injection inr (" <> renderTerm a <> ") of a disjoint union (or ∨)."
  TApply f a -> "Application: (" <> renderTerm f <> ") (" <> renderTerm a <> "). Reduces by β when the function is a λ."
  TSpread p x y body ->
    "Spread (let 〈"
      <> varText x
      <> ", "
      <> varText y
      <> "〉 = "
      <> renderTerm p
      <> " in "
      <> renderTerm body
      <> "): eliminates a pair."
  TDecide d _ _ _ _ -> "Case analysis decide " <> renderTerm d <> " of a disjoint union."
  TList a -> "The type of lists of " <> renderTerm a <> "."
  TSet a x p ->
    "Set type {"
      <> varText x
      <> ":"
      <> renderTerm a
      <> " | "
      <> renderTerm p
      <> "}. Inhabitants are elements of A that satisfy P."
  TIsect a x b
    | isDummyVar x || not (occursFree x b) ->
        "Independent intersection "
          <> renderTerm a
          <> " ∩ "
          <> renderTerm b
          <> ", i.e. isect(A; _.B). A common realizer of B for every index of type A."
    | otherwise ->
        "Intersection type ⋂"
          <> varText x
          <> ":"
          <> renderTerm a
          <> ". "
          <> renderTerm b
          <> ". A common realizer of every B[a]; the index is not computational."
  TQuotient a x y e ->
    "Quotient type ("
      <> varText x
      <> ","
      <> varText y
      <> "):"
      <> renderTerm a
      <> " // "
      <> renderTerm e
      <> ". Members of A, with equality given by E."
  TSquash a ->
    "Squash ["
      <> renderTerm a
      <> "]: A with computational content hidden. Inhabited by Ax when A is inhabited."
  TAny v tyT -> "any " <> renderTerm v <> " " <> renderTerm tyT <> ": a term of type T from a proof of Void (ex falso)."
  TIntEq a b _ _ -> "int_eq: boolean case split on whether " <> renderTerm a <> " = " <> renderTerm b <> "."
  TLess a b _ _ -> "less: boolean case split on whether " <> renderTerm a <> " < " <> renderTerm b <> "."
  TAtomEq a b _ _ -> "atom_eq: boolean case split on whether " <> renderTerm a <> " = " <> renderTerm b <> " as tokens."
  TListInd lst _ _ _ _ _ -> "List induction on " <> renderTerm lst <> "."
  TInd n _ _ _ _ _ _ _ -> "Integer induction ind on " <> renderTerm n <> "."
  TVar (Var n) ->
    case lookupAbs lib n of
      Just a -> absNote a
      Nothing -> "Variable " <> n <> "."
  TOp (Operator oid _) _ ->
    case lookupAbs lib (opIdText oid) of
      Just a -> absNote a
      Nothing -> "Operator " <> opIdText oid <> " in uniform syntax."

absNote :: Abstraction -> Text
absNote a =
  let soft = if absSoft a then "Soft abstraction. " else "Abstraction. "
   in soft
        <> opIdText (absOpId a)
        <> " == "
        <> renderTerm (absRhs a)

explainRule :: Text -> Text
explainRule r
  | T.isPrefixOf "hyp" r =
      "Kernel rule hyp: the conclusion matches a hypothesis, so that hypothesis is the proof."
  | T.isPrefixOf "elim" r =
      "Kernel rule elim: use a hypothesis according to its type (Π-application, Σ-spread, ∨-decide, Void-elim, …)."
  | T.isPrefixOf "lemma" r =
      "Kernel rule lemma: bring a completed theorem into the hypothesis list."
  | T.isPrefixOf "cut" r =
      "Kernel rule cut: assert an intermediate proposition, then use it."
  | T.isPrefixOf "thin" r =
      "Kernel rule thin: drop a hypothesis."
  | T.isPrefixOf "decide" r =
      "Kernel rule decide: case analysis on integer equality, integer comparison, or a union-typed term."
  | T.isPrefixOf "cumulativity" r =
      "Kernel rule cumulativity: a type in U{i} inhabits every larger universe."
  | r == "intro" =
      "Kernel rule intro: inhabit the conclusion by introducing its principal constructor (λ, pair, Ax, inl/inr, …)."
  | r == "eq" =
      "Kernel rule eq: canonical equality and membership (computation, constructor injectivity, hypothesis)."
  | r == "compute" =
      "Kernel rule compute: weak-head reduce the conclusion."
  | otherwise =
      "Primitive refinement rule " <> r <> ". Tactics search for trees of such rules; they are not themselves trusted."

explainTactic :: TacticExpr -> Text
explainTactic = \case
  TxId -> "idtac: leave the goal unchanged."
  TxFail -> "fail: the tactic that always fails."
  TxIntro (IxInfer Nothing) -> "intro: inhabit the conclusion (λ, pair, Ax, …) with an inferred binder name."
  TxIntro (IxInfer (Just x)) -> "intro " <> varText x <> ": introduce the principal constructor, naming the binder " <> varText x <> "."
  TxIntro IxLeft -> "intro left / left: choose the left injection of a disjoint union or disjunction."
  TxIntro IxRight -> "intro right / right: choose the right injection of a disjoint union or disjunction."
  TxIntro (IxWitness _) -> "intro with t: supply a witness for ∃ / Σ / a set type."
  TxElim i Nothing -> "elim " <> tshow i <> ": eliminate hypothesis " <> tshow i <> " according to its type."
  TxElim i (Just _) -> "elim " <> tshow i <> " with t: instantiate a Π / ∀ / ⋂ hypothesis."
  TxHyp Nothing -> "hyp: search the hypotheses for one that proves the conclusion."
  TxHyp (Just i) -> "hyp " <> tshow i <> ": use hypothesis " <> tshow i <> "."
  TxAuto -> "auto: bounded proof search (hyp, eq, intro, elim, compute). Depth defaults to 6."
  TxAutoN n -> "auto " <> tshow n <> ": bounded proof search of depth " <> tshow n <> "."
  TxD Nothing -> "D: decompose the conclusion."
  TxD (Just i) -> "D " <> tshow i <> ": decompose clause " <> tshow i <> " (0 = conclusion)."
  TxEq -> "eq: canonical equality / membership."
  TxCompute -> "compute: weak-head reduce the conclusion."
  TxReduce -> "reduce: repeat compute."
  TxUnfold -> "unfold: unfold a soft encoding or abstraction in the conclusion."
  TxArith -> "arith: decide a closed integer equality by computation."
  TxProveProp -> "prove_prop: propositional tableau, implemented via auto."
  TxLeft -> "left: intro left."
  TxRight -> "right: intro right."
  TxSplit -> "split: introduce a non-dependent pair / conjunction."
  TxExists _ -> "exists t: provide an existential witness."
  TxAssumption -> "assumption: synonym for hyp."
  TxCut {} -> "cut T: assert T as an intermediate goal."
  TxLemma n _ -> "lemma " <> n <> ": use a completed theorem."
  TxThin i -> "thin " <> tshow i <> ": drop hypothesis " <> tshow i <> "."
  TxDecideInt {} -> "decide a = b: case analysis on integer equality (the two cases are a = b and ¬(a = b))."
  TxDecideLt {} -> "decide a < b: case analysis on integer comparison."
  TxCases _ -> "decide t: case analysis on a union-typed term."
  TxThen a b ->
    prettyTacticExpr a <> " THEN " <> prettyTacticExpr b <> ": run the second tactic on every new subgoal of the first."
  TxThenL a _ ->
    prettyTacticExpr a <> " THENL […]: one tactic per immediate subgoal."
  TxOrElse a b ->
    prettyTacticExpr a <> " ORELSE " <> prettyTacticExpr b <> ": try the first tactic; on failure, the second."
  TxRepeat a -> "REPEAT " <> prettyTacticExpr a <> ": apply until failure (always succeeds)."
  TxTry a -> "TRY " <> prettyTacticExpr a <> ": t ORELSE idtac."
  TxSeq ts -> "Sequential composition of " <> tshow (length ts) <> " tactic steps (THEN)."

tshow :: (Show a) => a -> Text
tshow = T.pack . show
