-- | Parsers for terms, tactic scripts, and theory files.
--
-- The term language accepts both Unicode and ASCII connectives. Pretty-printed
-- terms (see "Nuprl.Pretty") are valid input.
module Nuprl.Parse
  ( Parser
  , parseTerm
  , parseTermAt
  , parseTactic
  , parseTacticAt
  , parseTheory
  , parseTheoryAt
  , parseLevel
  ) where

import Control.Monad (void, when)
import Control.Monad.Combinators.Expr
import Data.Char (isAlphaNum, isUpper)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void)
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as L

import Nuprl.Error
import Nuprl.Library (Abstraction (..), Object (..), Status (..), Theorem (..), Theory (..))
import Nuprl.Tactic
import Nuprl.Term

-- | Parser over 'Text' with no custom error component.
type Parser = Parsec Void Text

--------------------------------------------------------------------------------
-- Public entry points
--------------------------------------------------------------------------------

parseTerm :: Text -> Either NuprlError Term
parseTerm = parseTermAt "<term>"

parseTermAt :: FilePath -> Text -> Either NuprlError Term
parseTermAt = runP (sc *> pTerm <* eof)

parseTactic :: Text -> Either NuprlError TacticExpr
parseTactic = parseTacticAt "<tactic>"

parseTacticAt :: FilePath -> Text -> Either NuprlError TacticExpr
parseTacticAt = runP (sc *> pTacticTop <* eof)

parseTheory :: Text -> Either NuprlError Theory
parseTheory = parseTheoryAt "<theory>"

parseTheoryAt :: FilePath -> Text -> Either NuprlError Theory
parseTheoryAt = runP (sc *> pTheory <* eof)

parseLevel :: Text -> Either NuprlError LevelExp
parseLevel = runP (sc *> pLevel <* eof) "<level>"

runP :: Parser a -> FilePath -> Text -> Either NuprlError a
runP p fp input =
  case parse p fp input of
    Left e -> Left (ErrParse (T.pack (errorBundlePretty e)))
    Right a -> Right a

--------------------------------------------------------------------------------
-- Lexer
--------------------------------------------------------------------------------

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

-- | Keyword that must not be a prefix of an identifier.
keyword :: Text -> Parser ()
keyword w = lexeme . try $ do
  _ <- string w
  notFollowedBy identChar

identChar :: Parser Char
identChar = satisfy (\c -> isAlphaNum c || c == '_' || c == '\'') <?> "identifier character"

identStart :: Parser Char
identStart = letterChar <|> char '_'

-- | Identifier that may be a reserved word (used for library object names).
rawIdent :: Parser Text
rawIdent = lexeme . try $ do
  c <- identStart
  cs <- many identChar
  pure (T.pack (c : cs))

identifier :: Parser Text
identifier = lexeme . try $ do
  w <- do
    c <- identStart
    cs <- many identChar
    pure (T.pack (c : cs))
  when (w `elem` reserved) $
    fail ("reserved word " <> T.unpack w)
  pure w

reserved :: [Text]
reserved =
  [ "theory"
  , "import"
  , "abs"
  , "abstraction"
  , "theorem"
  , "proof"
  , "qed"
  , "soft"
  , "comment"
  , "True"
  , "False"
  , "Unit"
  , "Void"
  , "Int"
  , "Atom"
  , "Ax"
  , "List"
  , "inl"
  , "inr"
  , "decide"
  , "of"
  , "let"
  , "in"
  , "any"
  , "int_eq"
  , "less"
  , "atom_eq"
  , "list_ind"
  , "ind"
  , "fun"
  , "forall"
  , "exists"
  , "idtac"
  , "fail"
  , "intro"
  , "elim"
  , "hyp"
  , "auto"
  , "eq"
  , "compute"
  , "reduce"
  , "unfold"
  , "arith"
  , "prove_prop"
  , "left"
  , "right"
  , "split"
  , "assumption"
  , "cut"
  , "lemma"
  , "thin"
  , "with"
  , "THEN"
  , "THENL"
  , "ORELSE"
  , "REPEAT"
  , "TRY"
  ]

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

angles :: Parser a -> Parser a
angles = between (symbol "<") (symbol ">")

integer :: Parser Integer
integer = lexeme (L.signed sc L.decimal)

natural :: Parser Integer
natural = lexeme L.decimal

--------------------------------------------------------------------------------
-- Levels
--------------------------------------------------------------------------------

pLevel :: Parser LevelExp
pLevel = makeExprParser pLevelAtom levelOps
  where
    levelOps =
      [ [Postfix (LSucc <$ (symbol "'" <|> symbol "+1"))]
      , [InfixL (LMax <$ symbol "max")]
      ]
    -- `max` as infix is unusual; we also accept max(a,b) as an atom.

pLevelAtom :: Parser LevelExp
pLevelAtom =
  choice
    [ parens pLevel
    , do
        _ <- try (symbol "max")
        parens $ do
          a <- pLevel
          _ <- symbol ","
          LMax a <$> pLevel
    , LConst . fromInteger <$> try natural
    , LVar <$> identifier
    ]

-- Fix: Postfix for successor. Define a helper pattern.
pattern LSucc :: LevelExp -> LevelExp
pattern LSucc e = LAdd e 1

--------------------------------------------------------------------------------
-- Terms
--------------------------------------------------------------------------------

pTerm :: Parser Term
pTerm = pConnective

-- | Propositional connectives bind looser than equality, which binds looser
-- than arithmetic and @<@. So @x = y ∈ Int ∨ P@ is a disjunction of an
-- equality, not an equality at a union type. Binders are atoms, so
-- @A → ∀x:B. C@ parses.
pConnective :: Parser Term
pConnective = makeExprParser pConnectiveAtom opsProp
  where
    opsProp =
      [ [InfixR (tTimes <$ (symbol "×" <|> tryAndProd))]
      , [InfixR (TAnd <$ (symbol "∧" <|> symbol "/\\"))]
      , [InfixR (TUnion <$ (symbol "⊎" <|> symbol "+.")), InfixR (TOr <$ (symbol "∨" <|> symbol "\\/"))]
      , [InfixR (tArrow <$ arrowSym), InfixR (TImplies <$ (symbol "⇒" <|> symbol "=>"))]
      , [InfixR (TIff <$ (symbol "⇔" <|> symbol "<=>"))]
      ]

pConnectiveAtom :: Parser Term
pConnectiveAtom = pLam <|> pBinderTerm <|> pEqTerm

-- | The type annotation of @a = b ∈ T@ includes type formers (@⊎@, @×@, @→@)
-- but not propositional @∨@/@∧@/@⇒@, so @x = y ∈ Int ∨ P@ stays a disjunction
-- while @a = b ∈ True ⊎ True@ is an equality at a union type.
pTypeArg :: Parser Term
pTypeArg = makeExprParser pArith typeOps
  where
    typeOps =
      [ [InfixR (tTimes <$ symbol "×")]
      , [InfixR (TUnion <$ (symbol "⊎" <|> symbol "+."))]
      ]

-- | Equality @a = b ∈ T@ and membership @a ∈ T@.
pEqTerm :: Parser Term
pEqTerm = do
  a <- pArith
  choice
    [ try $ do
        _ <- symbol "="
        b <- pArith
        _ <- symbol "∈"
        ty <- pTypeArg
        pure (TEqual ty a b)
    , try $ do
        _ <- symbol "∈"
        ty <- pTypeArg
        pure (TMember a ty)
    , pure a
    ]

pLam :: Parser Term
pLam = do
  _ <- symbol "λ" <|> symbol "\\" <|> (keyword "fun" *> pure "fun")
  xs <- some pVar
  _ <- symbol "." <|> symbol "=>"
  body <- pTerm
  pure (foldr TLambda body xs)

pBinderTerm :: Parser Term
pBinderTerm =
  choice
    [ pForall
    , pExists
    , try pDepFun
    , try pDepProd
    ]

pForall :: Parser Term
pForall = do
  _ <- void (symbol "∀") <|> keyword "forall"
  (x, a) <- pTypedBinder
  _ <- symbol "."
  TAll a x <$> pTerm

pExists :: Parser Term
pExists = do
  _ <- void (symbol "∃") <|> keyword "exists"
  (x, a) <- pTypedBinder
  _ <- symbol "."
  TExists a x <$> pTerm

pTypedBinder :: Parser (Var, Term)
pTypedBinder =
  parens binder <|> binder
  where
    binder = do
      x <- pVar
      _ <- symbol ":"
      a <- pTerm
      pure (x, a)

-- | @(x:A) → B@
pDepFun :: Parser Term
pDepFun = do
  (x, a) <- parens $ do
    x <- pVar
    _ <- symbol ":"
    a <- pArrTerm
    pure (x, a)
  _ <- arrowSym
  TFunction a x <$> pTerm

pDepProd :: Parser Term
pDepProd = do
  (x, a) <- parens $ do
    x <- pVar
    _ <- symbol ":"
    a <- pArrTerm
    pure (x, a)
  _ <- symbol "×" <|> symbol "*"
  TProduct a x <$> pTerm

arrowSym :: Parser Text
arrowSym = symbol "→" <|> symbol "->"

pExpr :: Parser Term
pExpr = pConnective

pArith :: Parser Term
pArith = makeExprParser pApp ops
  where
    ops =
      [ [Prefix (foldr (.) id <$> some (TNot <$ (symbol "¬" <|> symbol "~")))]
      , [InfixR (TCons <$ symbol "::")]
      , [InfixL (TMul <$ tryMul), InfixL (TDiv <$ symbol "/")]
      , [InfixL (TAdd <$ tryPlus), InfixL (TSub <$ tryMinus)]
      , [InfixN (TLt <$ tryLt), InfixN (tLe <$ tryLe)]
      ]

tryMul :: Parser Text
tryMul = try $ do
  _ <- symbol "*"
  -- do not steal `*` if we already used it as product in another branch;
  -- both × and * are product at a lower precedence; `*` at this level is
  -- integer multiplication. This is ambiguous by design: `A * B` at type
  -- level is product, at term level is multiply. Users should use × for
  -- types and * for integers, but we parse * as multiply here (tighter)
  -- and × as product.
  pure "*"

tryAndProd :: Parser Text
tryAndProd = symbol "×" -- handled above; placeholder not used

tryPlus :: Parser Text
tryPlus = symbol "+" -- union is lower (looser) so + in arithmetic binds tighter...
-- WAIT: I put + as TAdd at tighter precedence AND TUnion at looser.
-- makeExprParser will try tighter first. So `A + B` is always TAdd.
-- That's a problem for A + B as union.
--
-- Fix: use `+` only for integers (TAdd) and `⊎` or `\/` for union.
-- Pretty prints union as `+`. Roundtrip would fail.
--
-- Better: pretty-print union as `A ⊎ B` or keep `A + B` for union when
-- arguments look like types. Too heuristic.
--
-- Decision: `+` is union/disjunction at the type/prop level AND addition
-- at the term level. The pretty printer uses `+` for both TAdd and TUnion.
-- Parser: `+` is TAdd (tighter). For union the user writes `A ⊎ B` or
-- `A \/ B` or `A ∨ B`. I'll pretty-print TUnion as `⊎` and TAdd as `+`.
--
-- I'll update Pretty.hs later. For now parse:
--   +  → TAdd
--   ⊎  → TUnion
--   ∨, \/ → TOr (which unfolds to union)

tryMinus :: Parser Text
tryMinus = symbol "-"

-- | @a < b@ as a type; do not steal @<=@, @<>@, or pair syntax @<a, b>@
-- (pairs are parsed as atoms).
tryLt :: Parser Text
tryLt = try . lexeme $ do
  _ <- char '<'
  notFollowedBy (char '>' <|> char '=')
  pure "<"

tryLe :: Parser Text
tryLe = symbol "≤" <|> symbol "<="

-- | @a ≤ b@ is the type @a < b + 1@.
tLe :: Term -> Term -> Term
tLe a b = TLt a (TAdd b (TNat 1))

pArrTerm :: Parser Term
pArrTerm = pExpr

pApp :: Parser Term
pApp = do
  f <- pAtom
  args <- many pAtom
  pure (tApps f args)

pAtom :: Parser Term
pAtom =
  choice
    [ parens pTerm
    , pPair
    , pListLit
    , pSet
    , pSquash
    , pLet
    , pDecide
    , pKeywordAtom
    , pUniverse
    , pProp
    , pToken
    , try pNat
    , pInlInr
    , pAny
    , pIntEq
    , pLess
    , pAtomEq
    , pListInd
    , pInd
    , try pUniformOp
    , TVar <$> pVar
    ]

pKeywordAtom :: Parser Term
pKeywordAtom =
  choice
    [ TTrue <$ keyword "True"
    , TFalse <$ keyword "False"
    , TUnit <$ keyword "Unit"
    , TVoid <$ keyword "Void"
    , TInt <$ keyword "Int"
    , TAtom <$ keyword "Atom"
    , TAxiom <$ keyword "Ax"
    , TNil <$ (void (symbol "[]") <|> keyword "nil")
    , do
        keyword "List"
        TList <$> pAtom
    ]

pUniverse :: Parser Term
pUniverse = do
  _ <- lexeme . try $ string "U" <* notFollowedBy identChar
  TUniverse <$> braces pLevel

pProp :: Parser Term
pProp = do
  _ <- lexeme . try $ string "P" <* notFollowedBy identChar
  TProp <$> braces pLevel

pToken :: Parser Term
pToken = lexeme $ do
  _ <- char '"'
  s <- manyTill L.charLiteral (char '"')
  pure (TToken (T.pack s))

pNat :: Parser Term
pNat = TNat <$> natural

pVar :: Parser Var
pVar = Var <$> identifier <|> (Var "_" <$ symbol "_")

pPair :: Parser Term
pPair = try . angles $ do
  a <- pTerm
  _ <- symbol ","
  TPair a <$> pTerm

pListLit :: Parser Term
pListLit = try . brackets $ do
  xs <- pTerm `sepBy` symbol ","
  pure (foldr TCons TNil xs)

pSet :: Parser Term
pSet = try . braces $ do
  x <- pVar
  _ <- symbol ":"
  a <- pTerm
  _ <- symbol "|"
  TSet a x <$> pTerm

pSquash :: Parser Term
pSquash = try $ do
  t <- brackets pTerm
  -- Distinguish from list literals: a squash is [T] with a single term and
  -- no commas. pListLit is `try` as well; we put squash after list in
  -- pAtom... actually list is first. `[A]` would parse as a singleton list.
  -- Squash is more important for the type theory. Parse `[T]` as squash,
  -- and lists as `[]` / `h::t` / `[a, b, ...]`.
  -- We already consumed via a different branch. See pAtom order:
  -- pListLit is before pSquash. I'll swap: pSquash for `[t]` without comma,
  -- pListLit for `[t, ...]` or `[]`.
  pure (TSquash t)

-- Revisit list vs squash: I'll handle both in one parser.
-- (The pListLit / pSquash split is messy.) Let's replace with pBrackTerm.

pLet :: Parser Term
pLet = do
  keyword "let"
  (x, y) <- angles $ do
    x <- pVar
    _ <- symbol ","
    y <- pVar
    pure (x, y)
  _ <- symbol "="
  p <- pTerm
  keyword "in"
  TSpread p x y <$> pTerm

pDecide :: Parser Term
pDecide = do
  keyword "decide"
  d <- pTerm
  keyword "of"
  keyword "inl"
  x <- pVar
  _ <- symbol "=>"
  t <- pTerm
  _ <- symbol "|"
  keyword "inr"
  y <- pVar
  _ <- symbol "=>"
  TDecide d x t y <$> pTerm

pInlInr :: Parser Term
pInlInr =
  choice
    [ do keyword "inl"; TInl <$> pAtom
    , do keyword "inr"; TInr <$> pAtom
    ]

pAny :: Parser Term
pAny = do
  keyword "any"
  v <- pAtom
  TAny v <$> pAtom

pIntEq :: Parser Term
pIntEq = do
  keyword "int_eq"
  TIntEq <$> pAtom <*> pAtom <*> pAtom <*> pAtom

pLess :: Parser Term
pLess = do
  keyword "less"
  TLess <$> pAtom <*> pAtom <*> pAtom <*> pAtom

pAtomEq :: Parser Term
pAtomEq = do
  keyword "atom_eq"
  TAtomEq <$> pAtom <*> pAtom <*> pAtom <*> pAtom

pListInd :: Parser Term
pListInd = do
  keyword "list_ind"
  lst <- pAtom
  base <- pAtom
  parens $ do
    x <- pVar
    _ <- symbol ","
    xs <- pVar
    _ <- symbol ","
    ih <- pVar
    _ <- symbol "."
    step <- pTerm
    pure (TListInd lst base x xs ih step)

-- | @ind(n; x,ih.down; base; y,jh.up)@, matching NuPRL integer induction.
pInd :: Parser Term
pInd = do
  keyword "ind"
  parens $ do
    n <- pTerm
    _ <- symbol ";"
    x <- pVar
    _ <- symbol ","
    ih <- pVar
    _ <- symbol "."
    down <- pTerm
    _ <- symbol ";"
    base <- pTerm
    _ <- symbol ";"
    y <- pVar
    _ <- symbol ","
    jh <- pVar
    _ <- symbol "."
    up <- pTerm
    pure (TInd n x ih down base y jh up)

-- | Uniform syntax: @opid{params}(bterms)@ or @Opid(bterms)@.
--
-- A lowercase identifier followed by a single unbinding argument, as in
-- @g (f x)@, is juxtaposition (application), not a uniform operator. Use a
-- capitalised name (@Fin(n)@), a parameter brace (@id{}(x)@), a semicolon
-- (@Equipollent(A; B)@), or an explicit binder (@opid(x.t)@) for operators.
pUniformOp :: Parser Term
pUniformOp = try $ do
  oidTxt <- identifier
  let oid = OpId oidTxt
  params <- option [] (braces (pParam `sepBy` symbol ";"))
  bts <- parens (pBound `sepBy` symbol ";")
  let capitalized = case T.uncons oidTxt of
        Just (c, _) -> isUpper c
        Nothing -> False
      looksLikeApp =
        null params
          && not capitalized
          && length bts == 1
          && all (null . btVars) bts
  when looksLikeApp $
    fail "application, not a uniform operator"
  pure (TOp (Operator oid params) bts)

pParam :: Parser Parameter
pParam =
  choice
    [ LevelParam <$> try (pLevel <* (symbol ":l" <|> symbol ":L"))
    , NatParam <$> try (integer <* (symbol ":n" <|> symbol ":N"))
    , TokenParam <$> try (pRawToken <* (symbol ":t" <|> symbol ":T"))
    , VarParam <$> try (pVar <* (symbol ":v" <|> symbol ":V"))
    , LevelParam <$> pLevel
    , NatParam <$> integer
    ]

pRawToken :: Parser Text
pRawToken = identifier

pBound :: Parser BoundTerm
pBound = do
  vs <- option [] . try $ do
    xs <- pVar `sepBy1` symbol ","
    _ <- symbol "."
    pure xs
  BoundTerm vs <$> pTerm

--------------------------------------------------------------------------------
-- Membership / equality as postfix on atoms, handled inside pApp via a
-- dedicated parser wrapping pExpr... we add a layer.
--------------------------------------------------------------------------------

-- Equality `a = b ∈ T` and membership `a ∈ T` are parsed as a suffix of
-- pExpr. We hook this by replacing pTerm's expr path.

-- Actually pTerm = pLam <|> pBinderTerm <|> pExpr, and pExpr never sees `=`.
-- Add pEqTerm.

-- I'll redefine pTerm at the bottom of the term section by inserting pEq
-- between binders and expr. Because Haskell doesn't allow redefinition,
-- I already used pTerm in many places. Let me add equality inside pExpr
-- using postfix operators... ternary is hard.
--
-- Wrap: pTerm currently calls pExpr. Change pTerm to call pEqTerm.

-- I'll use a different approach in pAtom after parsing an application:
-- not easy.
--
-- Let's patch pTerm by making pExpr call pEqApp.

-- WAIT I already defined pTerm. I need to edit the definition.
-- I'll add pEqTerm and change pTerm... I cannot change without replacing.
-- The write already has pTerm = pLam <|> pBinderTerm <|> pExpr.
--
-- I'll parse equality as InfixN in makeExprParser:
--   a = b  is incomplete; we need ∈ T.
--
-- Custom: after pExpr, optionally parse `= term ∈ term` or `∈ term`.

-- I'll handle this with a local wrapper used as pTerm. Since pTerm is already
-- defined, I'll add the suffix parser as pTerm itself... too late.
--
-- Fix: change pExpr to pEqExpr.

-- I'll implement pEqSuffix as a combinator used at the start:

-- Actually the simplest fix: in this file, replace pTerm's third alt.
-- I'll do a search_replace after writing.

--------------------------------------------------------------------------------
-- Tactics
--------------------------------------------------------------------------------

pTacticTop :: Parser TacticExpr
pTacticTop = pTacticSeq

pTacticSeq :: Parser TacticExpr
pTacticSeq = do
  ts <- pTacticOrElse `sepBy1` (symbol ";" <|> try (lookAhead pTacticStart *> pure ";"))
  -- Newlines: sc already consumed them. Sequential tactics in a proof block
  -- are separated by semicolons OR by simply being on the next line when
  -- used from pProofBlock. Here, `sepBy1` with `;` is the expression parser.
  pure (case ts of [t] -> t; _ -> TxSeq ts)

pTacticStart :: Parser ()
pTacticStart = void (choice (map (try . keyword) tacticKws))

tacticKws :: [Text]
tacticKws =
  [ "idtac"
  , "fail"
  , "intro"
  , "elim"
  , "hyp"
  , "auto"
  , "eq"
  , "compute"
  , "reduce"
  , "unfold"
  , "arith"
  , "prove_prop"
  , "left"
  , "right"
  , "split"
  , "assumption"
  , "cut"
  , "lemma"
  , "thin"
  , "exists"
  , "decide"
  , "REPEAT"
  , "TRY"
  , "D"
  ]

pTacticOrElse :: Parser TacticExpr
pTacticOrElse = makeExprParser pTacticAtom tacticOps
  where
    tacticOps =
      [ [Prefix (TxRepeat <$ keyword "REPEAT"), Prefix (TxTry <$ keyword "TRY")]
      , [Postfix pThenLPost]
      , [InfixR (TxThen <$ keyword "THEN")]
      , [InfixR (TxOrElse <$ keyword "ORELSE")]
      ]

pThenLPost :: Parser (TacticExpr -> TacticExpr)
pThenLPost = do
  keyword "THENL"
  ts <- brackets (pTacticTop `sepBy` symbol ",")
  pure (`TxThenL` ts)

pTacticAtom :: Parser TacticExpr
pTacticAtom =
  choice
    [ parens pTacticTop
    , TxId <$ keyword "idtac"
    , TxFail <$ keyword "fail"
    , pIntro
    , pElim
    , pHyp
    , pAuto
    , TxEq <$ keyword "eq"
    , TxCompute <$ keyword "compute"
    , TxReduce <$ keyword "reduce"
    , TxUnfold <$ keyword "unfold"
    , TxArith <$ keyword "arith"
    , TxProveProp <$ keyword "prove_prop"
    , TxLeft <$ keyword "left"
    , TxRight <$ keyword "right"
    , TxSplit <$ keyword "split"
    , TxAssumption <$ keyword "assumption"
    , pExistsTac
    , pCut
    , pLemma
    , pThin
    , pD
    , pDecideTac
    ]

pIntro :: Parser TacticExpr
pIntro = do
  keyword "intro"
  arg <-
    option
      (IxInfer Nothing)
      ( choice
          [ IxLeft <$ keyword "left"
          , IxRight <$ keyword "right"
          , IxWitness <$> (keyword "with" *> pTerm)
          , IxInfer . Just <$> pVar
          ]
      )
  pure (TxIntro arg)

pElim :: Parser TacticExpr
pElim = do
  keyword "elim"
  i <- fromInteger <$> natural
  m <- optional (keyword "with" *> pTerm)
  pure (TxElim i m)

pHyp :: Parser TacticExpr
pHyp = do
  keyword "hyp"
  TxHyp <$> optional (fromInteger <$> natural)

pAuto :: Parser TacticExpr
pAuto = do
  keyword "auto"
  TxAutoN . fromInteger <$> natural <|> pure TxAuto

pExistsTac :: Parser TacticExpr
pExistsTac = do
  keyword "exists"
  TxExists <$> pTerm

pCut :: Parser TacticExpr
pCut = do
  keyword "cut"
  ty <- pTerm
  mx <- optional (keyword "as" *> pVar)
  pure (TxCut ty mx)

pLemma :: Parser TacticExpr
pLemma = do
  keyword "lemma"
  n <- identifier
  args <- option [] (brackets (pTerm `sepBy` symbol ","))
  pure (TxLemma n args)

pThin :: Parser TacticExpr
pThin = do
  keyword "thin"
  TxThin . fromInteger <$> natural

pD :: Parser TacticExpr
pD = do
  _ <- void (symbol "D") <|> keyword "d"
  TxD <$> optional (fromInteger <$> natural)

-- | @decide a = b@, @decide a < b@, or @decide t@ (cases on a union).
-- Comparison and equality are parsed from applications so that @decide 0 < n@
-- is not read as case analysis on the type @0 < n@.
pDecideTac :: Parser TacticExpr
pDecideTac = do
  keyword "decide"
  choice
    [ try $ do
        a <- pApp
        _ <- symbol "="
        b <- pApp
        _ <- optional (void (symbol "∈" *> pExpr) <|> void (keyword "in" *> pExpr))
        pure (TxDecideInt a b)
    , try $ do
        a <- pApp
        _ <- tryLt
        b <- pApp
        pure (TxDecideLt a b)
    , TxCases <$> pExpr
    ]

--------------------------------------------------------------------------------
-- Theory files
--------------------------------------------------------------------------------

pTheory :: Parser Theory
pTheory = do
  keyword "theory"
  name <- identifier
  imports <- many pImport
  objs <- many pObject
  pure
    Theory
      { theoryName = name
      , theoryImports = imports
      , theoryObjects = objs
      }

pImport :: Parser Name
pImport = keyword "import" *> identifier

pObject :: Parser (Name, Object)
pObject =
  choice
    [ pAbs
    , pTheorem
    , pComment
    , pSoft
    ]

pAbs :: Parser (Name, Object)
pAbs = do
  keyword "abs" <|> keyword "abstraction"
  -- abs Name(binders) == term
  -- or abs Name == term
  oid <- rawIdent
  formals <- option [] (parens (pBound `sepBy` symbol ";"))
  _ <- symbol "==" <|> symbol ":="
  rhs <- pTerm
  let obj =
        ObjAbs
          Abstraction
            { absOpId = OpId oid
            , absFormals = formals
            , absRhs = rhs
            , absSoft = False
            }
  pure (oid, obj)

pTheorem :: Parser (Name, Object)
pTheorem = do
  keyword "theorem"
  name <- rawIdent
  _ <- symbol ":"
  goal <- pTerm
  keyword "proof"
  script <- pProofBlock
  keyword "qed"
  pure
    ( name
    , ObjTheorem
        Theorem
          { thmGoal = goal
          , thmScript = script
          , thmStatus = StatusRaw
          , thmExtract = Nothing
          }
    )

pProofBlock :: Parser TacticExpr
pProofBlock = do
  -- One tactic expression per line, composed with THEN, until `qed`.
  ts <- many (try (notFollowedBy (keyword "qed") *> pTacticLine))
  pure (TxSeq ts)

pTacticLine :: Parser TacticExpr
pTacticLine = pTacticOrElse <* optional (symbol ";")

pComment :: Parser (Name, Object)
pComment = do
  keyword "comment"
  name <- option "comment" identifier
  txt <- pStringLit <|> (T.unwords <$> some identifier)
  pure (name, ObjComment txt)

pStringLit :: Parser Text
pStringLit = lexeme $ do
  _ <- char '"'
  s <- manyTill L.charLiteral (char '"')
  pure (T.pack s)

pSoft :: Parser (Name, Object)
pSoft = do
  keyword "soft"
  names <- rawIdent `sepBy1` symbol ","
  -- Represented as a comment-like marker; Check will flip absSoft.
  pure ("soft:" <> T.intercalate "," names, ObjSoft names)

-- ObjSoft must exist in Library. I'll add it.

--------------------------------------------------------------------------------
-- Equality suffix: patched in via a note
--
-- We still need `a = b ∈ T`. I'll parse it as a top-level alternative of
-- pExpr by changing makeExprParser to include a postfix. Done in a follow-up
-- edit of pTerm.
--------------------------------------------------------------------------------
