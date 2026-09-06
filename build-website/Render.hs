-- | HTML rendering of terms, sequents, tactics, proofs, and source. Every
-- interesting node carries precomputed CLI analyses (pretty, uniform, WHNF,
-- unfold) as data attributes for the hover inspector.
module Render
  ( renderTermH
  , renderSequentH
  , renderTacticH
  , renderScriptH
  , renderProofH
  , renderSourceH
  , termAttrs
  ) where

import Data.Char (isAlphaNum, isDigit)
import Data.Text (Text)
import Data.Text qualified as T

import Analyze
import Html
import Nuprl.Compute (normalize, whnf)
import Nuprl.Library (Library)
import Nuprl.Pretty (renderTerm)
import Nuprl.Proof
import Nuprl.Sequent
import Nuprl.Subst (alphaEq, occursFree)
import Nuprl.Tactic (IntroArgExpr (..), TacticExpr (..))
import Nuprl.Term

--------------------------------------------------------------------------------
-- Terms
--------------------------------------------------------------------------------

renderTermH :: Library -> Term -> Html
renderTermH lib = annTerm True lib 0

-- | @True@ attaches CLI analyses (uniform, WHNF, unfold) to this node; children
-- keep semantic colour and a short note so the HTML stays small enough to ship.
annTerm :: Bool -> Library -> Int -> Term -> Html
annTerm heavy lib prec t =
  let body = termBody lib prec t
   in if heavy then wrap heavy lib t body else body

wrap :: Bool -> Library -> Term -> Html -> Html
wrap heavy lib t body = el "span" (termAttrs heavy lib t) body

termAttrs :: Bool -> Library -> Term -> [(Text, Text)]
termAttrs heavy lib t =
  let k = termKind lib t
      note = explainTerm lib t
      light =
        [ ("class", "tm " <> kindClass k)
        , ("data-kind", kindLabel k)
        , ("data-note", shorten 200 note)
        ]
   in if not heavy
        then light
        else
          let uni = uniformTerm t
              w = whnf t
              u = unfoldAny lib t
              nf =
                if termSize t <= 40
                  then
                    let n = normalize t
                     in if alphaEq n t || alphaEq n w then Nothing else Just n
                  else Nothing
              attr p name v = if p then [(name, shorten 320 v)] else []
           in light
                ++ attr (termSize t <= 64) "data-uniform" uni
                ++ attr (not (alphaEq w t) && termSize t <= 64) "data-whnf" (renderTerm w)
                ++ maybe [] (\t' -> attr (termSize t <= 64) "data-unfold" (renderTerm t')) u
                ++ maybe [] (\t' -> attr True "data-nf" (renderTerm t')) nf

-- Children of a displayed term: colour and a short note, no dump/compute payload.
sub :: Library -> Int -> Term -> Html
sub lib = annTerm False lib

termBody :: Library -> Int -> Term -> Html
termBody lib prec t = case t of
  TVar v -> varH v
  TUniverse l ->
    kw "U" <> raw "{" <> el "span" [("class", "sem-num")] (txt (prettyLevel l)) <> raw "}"
  TProp l ->
    kw "P" <> raw "{" <> el "span" [("class", "sem-num")] (txt (prettyLevel l)) <> raw "}"
  TVoid -> ty "Void"
  TUnit -> ty "Unit"
  TAxiom -> val "Ax"
  TInt -> ty "Int"
  TAtom -> ty "Atom"
  TTrue -> ty "True"
  TFalse -> ty "False"
  TNat n -> el "span" [("class", "sem-num")] (txt (T.pack (show n)))
  TToken s -> el "span" [("class", "sem-val")] (txt ("\"" <> s <> "\""))
  TNil -> val "[]"
  TLambda x b ->
    paren (prec > 0) $
      kw "λ" <> binder x <> raw "." <> sp <> sub lib 0 b
  TAll a x b ->
    paren (prec > 0) $
      conn "∀" <> binder x <> raw ":" <> sub lib 8 a <> raw "." <> sp <> sub lib 0 b
  TExists a x b ->
    paren (prec > 0) $
      conn "∃" <> binder x <> raw ":" <> sub lib 8 a <> raw "." <> sp <> sub lib 0 b
  TNot a ->
    paren (prec > 8) $ conn "¬" <> sub lib 8 a
  TImplies a b ->
    paren (prec > 1) $ sub lib 2 a <> sp <> conn "⇒" <> sp <> sub lib 1 b
  TOr a b ->
    paren (prec > 2) $ sub lib 3 a <> sp <> conn "∨" <> sp <> sub lib 2 b
  TLt a b ->
    paren (prec > 4) $ sub lib 5 a <> sp <> conn "<" <> sp <> sub lib 5 b
  TAnd a b ->
    paren (prec > 3) $ sub lib 4 a <> sp <> conn "∧" <> sp <> sub lib 3 b
  TIff a b ->
    paren (prec > 1) $ sub lib 2 a <> sp <> conn "⇔" <> sp <> sub lib 2 b
  TFunction a x b
    | isDummyVar x || not (occursFree x b) ->
        paren (prec > 1) $ sub lib 2 a <> sp <> conn "→" <> sp <> sub lib 1 b
    | otherwise ->
        paren (prec > 1) $
          raw "("
            <> binder x
            <> raw ":"
            <> sub lib 0 a
            <> raw ")"
            <> sp
            <> conn "→"
            <> sp
            <> sub lib 1 b
  TProduct a x b
    | isDummyVar x || not (occursFree x b) ->
        paren (prec > 3) $ sub lib 4 a <> sp <> conn "×" <> sp <> sub lib 3 b
    | otherwise ->
        paren (prec > 3) $
          raw "("
            <> binder x
            <> raw ":"
            <> sub lib 0 a
            <> raw ")"
            <> sp
            <> conn "×"
            <> sp
            <> sub lib 1 b
  TUnion a b ->
    paren (prec > 2) $ sub lib 3 a <> sp <> conn "⊎" <> sp <> sub lib 2 b
  TEqual tyT a b
    | alphaHead a b ->
        sub lib 8 a <> sp <> conn "∈" <> sp <> sub lib 5 tyT
    | otherwise ->
        paren (prec > 4) $
          sub lib 5 a <> sp <> conn "=" <> sp <> sub lib 5 b
            <> sp
            <> conn "∈"
            <> sp
            <> sub lib 5 tyT
  TMember tm tyT ->
    sub lib 8 tm <> sp <> conn "∈" <> sp <> sub lib 5 tyT
  TAdd a b ->
    paren (prec > 5) $ sub lib 5 a <> sp <> conn "+" <> sp <> sub lib 6 b
  TSub a b ->
    paren (prec > 5) $ sub lib 5 a <> sp <> conn "−" <> sp <> sub lib 6 b
  TMul a b ->
    paren (prec > 6) $ sub lib 6 a <> sp <> conn "·" <> sp <> sub lib 7 b
  TDiv a b ->
    paren (prec > 6) $ sub lib 6 a <> sp <> conn "/" <> sp <> sub lib 7 b
  TRem a b ->
    paren (prec > 6) $ sub lib 6 a <> sp <> conn "%" <> sp <> sub lib 7 b
  TMinus a ->
    paren (prec > 8) $ conn "−" <> sub lib 8 a
  TCons h tl ->
    paren (prec > 7) $ sub lib 8 h <> sp <> conn "::" <> sp <> sub lib 7 tl
  TPair a b ->
    raw "〈" <> sub lib 0 a <> raw "," <> sp <> sub lib 0 b <> raw "〉"
  TInl a ->
    paren (prec > 8) $ kw "inl" <> sp <> sub lib 9 a
  TInr a ->
    paren (prec > 8) $ kw "inr" <> sp <> sub lib 9 a
  TApply f a ->
    paren (prec > 8) $ sub lib 8 f <> sp <> sub lib 9 a
  TSpread p x y body ->
    paren (prec > 0) $
      kw "let"
        <> sp
        <> raw "〈"
        <> binder x
        <> raw ","
        <> sp
        <> binder y
        <> raw "〉"
        <> sp
        <> conn "="
        <> sp
        <> sub lib 0 p
        <> sp
        <> kw "in"
        <> sp
        <> sub lib 0 body
  TDecide d x left y right ->
    paren (prec > 0) $
      kw "decide"
        <> sp
        <> sub lib 0 d
        <> sp
        <> kw "of"
        <> sp
        <> kw "inl"
        <> sp
        <> binder x
        <> sp
        <> conn "⇒"
        <> sp
        <> sub lib 0 left
        <> sp
        <> conn "|"
        <> sp
        <> kw "inr"
        <> sp
        <> binder y
        <> sp
        <> conn "⇒"
        <> sp
        <> sub lib 0 right
  TList a ->
    paren (prec > 8) $ ty "List" <> sp <> sub lib 9 a
  TSet a x p ->
    raw "{"
      <> binder x
      <> raw ":"
      <> sub lib 0 a
      <> sp
      <> conn "|"
      <> sp
      <> sub lib 0 p
      <> raw "}"
  TIsect a x b
    | isDummyVar x ->
        paren (prec > 3) $ sub lib 4 a <> sp <> conn "∩" <> sp <> sub lib 3 b
    | otherwise ->
        paren (prec > 0) $
          conn "⋂" <> binder x <> raw ":" <> sub lib 8 a <> raw "." <> sp <> sub lib 0 b
  TSquash a ->
    raw "[" <> sub lib 0 a <> raw "]"
  TAny v tyT ->
    paren (prec > 8) $ kw "any" <> sp <> sub lib 9 v <> sp <> sub lib 9 tyT
  TIntEq a b th els ->
    paren (prec > 8) $
      kw "int_eq" <> sp <> sub lib 9 a <> sp <> sub lib 9 b
        <> sp
        <> sub lib 9 th
        <> sp
        <> sub lib 9 els
  TLess a b th els ->
    paren (prec > 8) $
      kw "less" <> sp <> sub lib 9 a <> sp <> sub lib 9 b
        <> sp
        <> sub lib 9 th
        <> sp
        <> sub lib 9 els
  TAtomEq a b th els ->
    paren (prec > 8) $
      kw "atom_eq" <> sp <> sub lib 9 a <> sp <> sub lib 9 b
        <> sp
        <> sub lib 9 th
        <> sp
        <> sub lib 9 els
  TListInd lst base x xs ih step ->
    paren (prec > 0) $
      kw "list_ind"
        <> sp
        <> sub lib 9 lst
        <> sp
        <> sub lib 9 base
        <> sp
        <> raw "("
        <> binder x
        <> raw ","
        <> binder xs
        <> raw ","
        <> binder ih
        <> raw "."
        <> sp
        <> sub lib 0 step
        <> raw ")"
  TInd n x ih down base y jh up ->
    paren (prec > 0) $
      kw "ind"
        <> raw "("
        <> sub lib 0 n
        <> raw ";"
        <> sp
        <> binder x
        <> raw ","
        <> binder ih
        <> raw "."
        <> sp
        <> sub lib 0 down
        <> raw ";"
        <> sp
        <> sub lib 0 base
        <> raw ";"
        <> sp
        <> binder y
        <> raw ","
        <> binder jh
        <> raw "."
        <> sp
        <> sub lib 0 up
        <> raw ")"
  TOp (Operator oid params) bts ->
    let name = opIdText oid
        nameH = el "span" [("class", kindClass (termKind lib t))] (txt name)
        pdoc
          | null params = emptyH
          | otherwise =
              raw "{"
                <> mconcat (punctuate (raw ";") (map (txt . prettyParam) params))
                <> raw "}"
        bdoc
          | null bts && null params = emptyH
          | otherwise =
              raw "("
                <> mconcat (punctuate (raw "; ") (map (prettyBound lib) bts))
                <> raw ")"
     in nameH <> pdoc <> bdoc

prettyParam :: Parameter -> Text
prettyParam = \case
  NatParam n -> T.pack (show n)
  TokenParam s -> "\"" <> s <> "\""
  StringParam s -> "\"" <> s <> "\""
  VarParam v -> varText v
  LevelParam l -> prettyLevel l

prettyBound :: Library -> BoundTerm -> Html
prettyBound lib (BoundTerm vs t) =
  binders <> sub lib 0 t
  where
    binders
      | null vs = emptyH
      | otherwise = mconcat (punctuate (raw ",") (map binder vs)) <> raw "."

alphaHead :: Term -> Term -> Bool
alphaHead (TVar x) (TVar y) = x == y
alphaHead a b = a == b

paren :: Bool -> Html -> Html
paren True h = raw "(" <> h <> raw ")"
paren False h = h

sp :: Html
sp = raw " "

kw :: Text -> Html
kw s = el "span" [("class", "sem-kw")] (txt s)

ty :: Text -> Html
ty s = el "span" [("class", "sem-type")] (txt s)

conn :: Text -> Html
conn s = el "span" [("class", "sem-conn")] (txt s)

val :: Text -> Html
val s = el "span" [("class", "sem-val")] (txt s)

binder :: Var -> Html
binder v =
  el
    "span"
    [ ("class", "sem-binder")
    , ("data-kind", "binder")
    , ("data-note", "Binding occurrence of " <> nm <> ".")
    ]
    (txt nm)
  where
    nm = if isDummyVar v then "_" else varText v

varH :: Var -> Html
varH v = el "span" [("class", "sem-var")] (txt nm)
  where
    nm = if isDummyVar v then "_" else varText v

punctuate :: Html -> [Html] -> [Html]
punctuate _ [] = []
punctuate _ [x] = [x]
punctuate s (x : xs) = x : s : punctuate s xs

--------------------------------------------------------------------------------
-- Sequents
--------------------------------------------------------------------------------

renderSequentH :: Library -> Sequent -> Html
renderSequentH lib sq =
  el "div" [("class", "sequent")] $
    ( if null (seqHyps sq)
        then emptyH
        else
          el "ol" [("class", "hyps")] $
            mconcat
              [ el "li" [("class", hypClass h), ("value", T.pack (show i))] (renderHyp lib i h)
              | (i, h) <- zip [1 ..] (seqHyps sq)
              ]
    )
      <> el
        "div"
        [("class", "concl")]
        ( el "span" [("class", "turnstile"), ("data-kind", "goal"), ("data-note", "The sequent turnstile: hypotheses above prove the conclusion.")] (txt "⊢")
            <> sp
            <> renderTermH lib (seqConcl sq)
        )

hypClass :: Hypothesis -> Text
hypClass h
  | hHidden h = "hyp hyp-hidden"
  | isHiddenVar (hVar h) = "hyp hyp-invisible"
  | otherwise = "hyp"

renderHyp :: Library -> Int -> Hypothesis -> Html
renderHyp lib i h =
  el "span" [("class", "hyp-idx")] (txt (T.pack (show i) <> "."))
    <> sp
    <> body
  where
    body
      | isHiddenVar (hVar h) || isDummyVar (hVar h) =
          renderTermH lib (hType h)
      | otherwise =
          binder (hVar h) <> sp <> conn ":" <> sp <> renderTermH lib (hType h)

--------------------------------------------------------------------------------
-- Tactics
--------------------------------------------------------------------------------

renderScriptH :: Library -> TacticExpr -> Html
renderScriptH lib = \case
  TxSeq ts ->
    el "ol" [("class", "script")] $
      mconcat [el "li" [] (renderTacticH lib t) | t <- ts]
  t -> el "div" [("class", "script")] (renderTacticH lib t)

renderTacticH :: Library -> TacticExpr -> Html
renderTacticH lib tx = wrapTac tx (tacBody lib tx)

wrapTac :: TacticExpr -> Html -> Html
wrapTac tx body =
  el
    "span"
    [ ("class", "tac " <> tacClass tx)
    , ("data-kind", "tactic")
    , ("data-note", explainTactic tx)
    ]
    body

tacClass :: TacticExpr -> Text
tacClass = \case
  TxThen {} -> "tac-comb"
  TxThenL {} -> "tac-comb"
  TxOrElse {} -> "tac-comb"
  TxRepeat {} -> "tac-comb"
  TxTry {} -> "tac-comb"
  TxSeq {} -> "tac-comb"
  _ -> "sem-tac"

tacBody :: Library -> TacticExpr -> Html
tacBody lib = \case
  TxId -> txt "idtac"
  TxFail -> txt "fail"
  TxIntro (IxInfer Nothing) -> txt "intro"
  TxIntro (IxInfer (Just x)) -> txt "intro " <> binder x
  TxIntro IxLeft -> txt "intro left"
  TxIntro IxRight -> txt "intro right"
  TxIntro (IxWitness t) -> txt "intro with " <> renderTermH lib t
  TxElim i Nothing -> txt ("elim " <> tshow i)
  TxElim i (Just t) -> txt ("elim " <> tshow i <> " with ") <> renderTermH lib t
  TxHyp Nothing -> txt "hyp"
  TxHyp (Just i) -> txt ("hyp " <> tshow i)
  TxAuto -> txt "auto"
  TxAutoN n -> txt ("auto " <> tshow n)
  TxD Nothing -> txt "D"
  TxD (Just i) -> txt ("D " <> tshow i)
  TxEq -> txt "eq"
  TxCompute -> txt "compute"
  TxReduce -> txt "reduce"
  TxUnfold -> txt "unfold"
  TxArith -> txt "arith"
  TxProveProp -> txt "prove_prop"
  TxLeft -> txt "left"
  TxRight -> txt "right"
  TxSplit -> txt "split"
  TxExists t -> txt "exists " <> renderTermH lib t
  TxAssumption -> txt "assumption"
  TxCut tyT mx ->
    txt "cut " <> renderTermH lib tyT
      <> maybe emptyH (\x -> txt " as " <> binder x) mx
  TxLemma n args ->
    txt ("lemma " <> n)
      <> if null args
        then emptyH
        else
          raw " ["
            <> mconcat (punctuate (raw ", ") (map (renderTermH lib) args))
            <> raw "]"
  TxThin i -> txt ("thin " <> tshow i)
  TxDecideInt a b ->
    txt "decide " <> renderTermH lib a <> sp <> conn "=" <> sp <> renderTermH lib b
  TxDecideLt a b ->
    txt "decide " <> renderTermH lib a <> sp <> conn "<" <> sp <> renderTermH lib b
  TxCases t -> txt "decide " <> renderTermH lib t
  TxThen a b ->
    renderTacticH lib a <> sp <> comb "THEN" <> sp <> renderTacticH lib b
  TxThenL a bs ->
    renderTacticH lib a
      <> sp
      <> comb "THENL"
      <> sp
      <> raw "["
      <> mconcat (punctuate (raw ", ") (map (renderTacticH lib) bs))
      <> raw "]"
  TxOrElse a b ->
    renderTacticH lib a <> sp <> comb "ORELSE" <> sp <> renderTacticH lib b
  TxRepeat a -> comb "REPEAT" <> sp <> renderTacticH lib a
  TxTry a -> comb "TRY" <> sp <> renderTacticH lib a
  TxSeq ts ->
    mconcat (punctuate (raw "; ") (map (renderTacticH lib) ts))

comb :: Text -> Html
comb s =
  el
    "span"
    [ ("class", "tac-comb")
    , ("data-kind", "tactic")
    , ("data-note", "LCF combinator " <> s <> ".")
    ]
    (txt s)

--------------------------------------------------------------------------------
-- Proof trees
--------------------------------------------------------------------------------

renderProofH :: Library -> Proof -> Html
renderProofH lib p =
  el "div" [("class", "proof-tree")] (renderNode lib True rootAddr p)

renderNode :: Library -> Bool -> Addr -> Proof -> Html
renderNode lib open addr = \case
  Unrefined sq ->
    el "div" [("class", "pnode open-goal")] $
      el "div" [("class", "pnode-head")] (txt "open goal")
        <> renderSequentH lib sq
  Refined sq name cs _extr ->
    let kids = zip [0 ..] cs
        summary =
          el "span" [("class", "rule"), ("data-kind", "tactic"), ("data-note", explainRule name)] (txt name)
            <> sp
            <> el "span" [("class", "turnstile")] (txt "⊢")
            <> sp
            <> el "span" [("class", "pnode-concl")] (txt (renderTerm (seqConcl sq)))
        extra =
          renderSequentH lib sq
            <> (if open then extractLine lib (Refined sq name cs _extr) else emptyH)
            <> ( if null kids
                   then emptyH
                   else
                     el "div" [("class", "subgoals")] $
                       mconcat
                         [ renderNode lib False (extendAddr addr i) c
                         | (i, c) <- kids
                         ]
               )
        attrs = [("class", "pnode")] ++ [("open", "open") | open]
     in el "details" attrs (el "summary" [] summary <> extra)

extractLine :: Library -> Proof -> Html
extractLine lib p =
  case extractProof p of
    Left _ -> emptyH
    Right e ->
      el "div" [("class", "node-extract")] $
        el "span" [("class", "k")] (txt "extract")
          <> sp
          <> el "span" [("class", "sem-extract")] (renderTermH lib e)

--------------------------------------------------------------------------------
-- Source highlighter
--------------------------------------------------------------------------------

renderSourceH :: Text -> Html
renderSourceH src =
  el "pre" [("class", "source")] (el "code" [] (highlight src))

highlight :: Text -> Html
highlight = go . T.unpack
  where
    go [] = emptyH
    go ('-' : '-' : rest) =
      let (cmt, more) = span (/= '\n') rest
       in el "span" [("class", "sem-comment")] (txt (T.pack ("--" <> cmt))) <> go more
    go ('{' : '-' : rest) =
      let (cmt, more) = breakBlock rest
       in el "span" [("class", "sem-comment")] (txt (T.pack ("{-" <> cmt))) <> go more
    go ('"' : rest) =
      let (s, more) = breakString rest
       in el "span" [("class", "sem-val")] (txt (T.pack ("\"" <> s))) <> go more
    go (c : rest)
      | isIdentStart c =
          let (w, more) = span isIdentChar rest
              tok = c : w
              cls = tokenClass (T.pack tok)
           in el "span" [("class", cls)] (txt (T.pack tok)) <> go more
      | isDigit c =
          let (w, more) = span isDigit rest
           in el "span" [("class", "sem-num")] (txt (T.pack (c : w))) <> go more
      | c `elem` ("∀∃λ¬∧∨⇒→×⊎∈⊢⇔" :: String) =
          el "span" [("class", "sem-conn")] (txt (T.singleton c)) <> go rest
      | otherwise = txt (T.singleton c) <> go rest

    isIdentStart c = isAlphaNum c || c == '_'
    isIdentChar c = isAlphaNum c || c == '_' || c == '\''

    breakBlock [] = ([], [])
    breakBlock ('-' : '}' : xs) = ("-}", xs)
    breakBlock (x : xs) = let (a, b) = breakBlock xs in (x : a, b)

    breakString [] = ([], [])
    breakString ('"' : xs) = ("\"", xs)
    breakString ('\\' : x : xs) = let (a, b) = breakString xs in ('\\' : x : a, b)
    breakString (x : xs) = let (a, b) = breakString xs in (x : a, b)

tokenClass :: Text -> Text
tokenClass w
  | w `elem` theoryKw = "sem-keyword"
  | w `elem` tacticKw = "sem-tac"
  | w `elem` typeKw = "sem-type"
  | w `elem` ctorKw = "sem-kw"
  | otherwise = "ident"

theoryKw :: [Text]
theoryKw =
  [ "theory"
  , "import"
  , "abs"
  , "abstraction"
  , "theorem"
  , "proof"
  , "qed"
  , "soft"
  , "comment"
  ]

tacticKw :: [Text]
tacticKw =
  [ "intro"
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
  , "idtac"
  , "fail"
  , "decide"
  , "exists"
  , "D"
  ]

typeKw :: [Text]
typeKw = ["True", "False", "Unit", "Void", "Int", "Atom", "List", "U", "P"]

ctorKw :: [Text]
ctorKw = ["Ax", "inl", "inr", "let", "in", "of", "any", "int_eq", "less", "atom_eq", "list_ind", "ind", "fun", "forall", "exists"]

tshow :: (Show a) => a -> Text
tshow = T.pack . show
