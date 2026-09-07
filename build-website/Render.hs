-- | HTML rendering of terms, sequents, tactics, proofs, and source. Every
-- surface-syntax piece (subterm, connective, binder, constructor, punctuation)
-- carries a hover payload so the inspector can pinpoint the glyph under the
-- pointer. Compound terms also wrap the whole phrase, so a gap between tokens
-- still describes that form.
module Render
  ( renderTermH
  , renderSequentH
  , renderTacticH
  , renderScriptH
  , renderProofH
  , renderSourceH
  , termAttrs
  , binder
  , tok
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

-- | Every node is wrapped. @heavy@ adds uniform / WHNF / unfold dumps; light
-- children still get kind, note, and the pretty surface string.
annTerm :: Bool -> Library -> Int -> Term -> Html
annTerm heavy lib prec t =
  wrap heavy lib t (termBody heavy lib prec t)

wrap :: Bool -> Library -> Term -> Html -> Html
wrap heavy lib t body = el "span" (termAttrs heavy lib t) body

termAttrs :: Bool -> Library -> Term -> [(Text, Text)]
termAttrs heavy lib t =
  let k = termKind lib t
      note = explainTerm lib t
      base =
        [ ("class", "tm " <> kindClass k)
        , ("data-kind", kindLabel k)
        , ("data-note", shorten 200 note)
        , ("data-surface", shorten 200 (renderTerm t))
        ]
      dump = heavy || termSize t <= 48
      attr p name v = if p then [(name, shorten 320 v)] else []
   in if not dump
        then base
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
           in base
                ++ attr (termSize t <= 80) "data-uniform" uni
                ++ attr (not (alphaEq w t) && termSize t <= 64) "data-whnf" (renderTerm w)
                ++ maybe [] (\t' -> attr (termSize t <= 64) "data-unfold" (renderTerm t')) u
                ++ maybe [] (\t' -> attr True "data-nf" (renderTerm t')) nf

-- | Subterms of a displayed term: same pinpointing, lighter analysis dump.
sub :: Library -> Int -> Term -> Html
sub lib = annTerm False lib

-- | Hoverable surface glyph that is not itself a term.
tok :: Kind -> Text -> Text -> Html
tok k glyph note =
  el
    "span"
    [ ("class", kindClass k)
    , ("data-kind", kindLabel k)
    , ("data-note", shorten 200 note)
    ]
    (txt glyph)

-- | Principal operator of @t@. Keeps the term's note / surface / uniform so
-- pointing at ∀, →, λ, … describes that form, while the class follows the
-- glyph (connective, constructor, …) for colour.
opGlyph :: Bool -> Library -> Term -> Kind -> Text -> Html
opGlyph heavy lib t vis glyph =
  el
    "span"
    ( ("class", kindClass vis)
        : ("data-kind", kindLabel vis)
        : [p | p@(name, _) <- termAttrs heavy lib t, name /= "class", name /= "data-kind"]
    )
    (txt glyph)

punct :: Text -> Text -> Html
punct = tok KPunct

termBody :: Bool -> Library -> Int -> Term -> Html
termBody heavy lib prec t = case t of
  TVar v -> txt (if isDummyVar v then "_" else varText v)
  TUniverse l ->
    opGlyph heavy lib t KType "U"
      <> punct "{" "Universe level subscript."
      <> tok KNum (prettyLevel l) ("Universe level " <> prettyLevel l <> ".")
      <> punct "}" "Universe level subscript."
  TProp l ->
    opGlyph heavy lib t KType "P"
      <> punct "{" "Propositional-universe level subscript."
      <> tok KNum (prettyLevel l) ("Universe level " <> prettyLevel l <> ".")
      <> punct "}" "Propositional-universe level subscript."
  TVoid -> txt "Void"
  TUnit -> txt "Unit"
  TAxiom -> txt "Ax"
  TInt -> txt "Int"
  TAtom -> txt "Atom"
  TTrue -> txt "True"
  TFalse -> txt "False"
  TNat n -> txt (T.pack (show n))
  TToken s -> txt ("\"" <> s <> "\"")
  TNil -> txt "[]"
  TLambda x b ->
    paren (prec > 0) $
      opGlyph heavy lib t KKw "λ" <> sp <> binder x <> dotSp <> sub lib 0 b
  TAll a x b ->
    paren (prec > 0) $
      opGlyph heavy lib t KConn "∀" <> sp <> binder x <> colon <> sub lib 8 a <> dotSp <> sub lib 0 b
  TExists a x b ->
    paren (prec > 0) $
      opGlyph heavy lib t KConn "∃" <> sp <> binder x <> colon <> sub lib 8 a <> dotSp <> sub lib 0 b
  TNot a ->
    paren (prec > 8) $ opGlyph heavy lib t KConn "¬" <> sp <> sub lib 8 a
  TImplies a b ->
    paren (prec > 1) $
      sub lib 2 a <> sp <> opGlyph heavy lib t KConn "⇒" <> sp <> sub lib 1 b
  TOr a b ->
    paren (prec > 2) $
      sub lib 3 a <> sp <> opGlyph heavy lib t KConn "∨" <> sp <> sub lib 2 b
  TLt a b ->
    paren (prec > 4) $
      sub lib 5 a <> sp <> opGlyph heavy lib t KConn "<" <> sp <> sub lib 5 b
  TAnd a b ->
    paren (prec > 3) $
      sub lib 4 a <> sp <> opGlyph heavy lib t KConn "∧" <> sp <> sub lib 3 b
  TIff a b ->
    paren (prec > 1) $
      sub lib 2 a <> sp <> opGlyph heavy lib t KConn "⇔" <> sp <> sub lib 2 b
  TFunction a x b
    | isDummyVar x || not (occursFree x b) ->
        paren (prec > 1) $
          sub lib 2 a <> sp <> opGlyph heavy lib t KConn "→" <> sp <> sub lib 1 b
    | otherwise ->
        paren (prec > 1) $
          punct "(" "Dependent function domain: (x : A) → B."
            <> binder x
            <> colon
            <> sub lib 0 a
            <> punct ")" "Dependent function domain: (x : A) → B."
            <> sp
            <> opGlyph heavy lib t KConn "→"
            <> sp
            <> sub lib 1 b
  TProduct a x b
    | isDummyVar x || not (occursFree x b) ->
        paren (prec > 3) $
          sub lib 4 a <> sp <> opGlyph heavy lib t KConn "×" <> sp <> sub lib 3 b
    | otherwise ->
        paren (prec > 3) $
          punct "(" "Dependent pair domain: (x : A) × B."
            <> binder x
            <> colon
            <> sub lib 0 a
            <> punct ")" "Dependent pair domain: (x : A) × B."
            <> sp
            <> opGlyph heavy lib t KConn "×"
            <> sp
            <> sub lib 1 b
  TUnion a b ->
    paren (prec > 2) $
      sub lib 3 a <> sp <> opGlyph heavy lib t KConn "⊎" <> sp <> sub lib 2 b
  TEqual tyT a b
    | alphaHead a b ->
        sub lib 8 a <> sp <> opGlyph heavy lib t KConn "∈" <> sp <> sub lib 5 tyT
    | otherwise ->
        paren (prec > 4) $
          sub lib 5 a
            <> sp
            <> opGlyph heavy lib t KConn "="
            <> sp
            <> sub lib 5 b
            <> sp
            <> tok KConn "∈" "Type of an equality: a = b ∈ A."
            <> sp
            <> sub lib 5 tyT
  TMember tm tyT ->
    sub lib 8 tm <> sp <> opGlyph heavy lib t KConn "∈" <> sp <> sub lib 5 tyT
  TAdd a b ->
    paren (prec > 5) $
      sub lib 5 a <> sp <> opGlyph heavy lib t KConn "+" <> sp <> sub lib 6 b
  TSub a b ->
    paren (prec > 5) $
      sub lib 5 a <> sp <> opGlyph heavy lib t KConn "−" <> sp <> sub lib 6 b
  TMul a b ->
    paren (prec > 6) $
      sub lib 6 a <> sp <> opGlyph heavy lib t KConn "·" <> sp <> sub lib 7 b
  TDiv a b ->
    paren (prec > 6) $
      sub lib 6 a <> sp <> opGlyph heavy lib t KConn "/" <> sp <> sub lib 7 b
  TRem a b ->
    paren (prec > 6) $
      sub lib 6 a <> sp <> opGlyph heavy lib t KConn "%" <> sp <> sub lib 7 b
  TMinus a ->
    paren (prec > 8) $ opGlyph heavy lib t KConn "−" <> sub lib 8 a
  TCons h tl ->
    paren (prec > 7) $
      sub lib 8 h <> sp <> opGlyph heavy lib t KConn "::" <> sp <> sub lib 7 tl
  TPair a b ->
    opGlyph heavy lib t KVal "〈"
      <> sp
      <> sub lib 0 a
      <> punct "," "Pair separator."
      <> sp
      <> sub lib 0 b
      <> sp
      <> tok KVal "〉" "Right angle of a pair 〈a, b〉."
  TInl a ->
    paren (prec > 8) $ opGlyph heavy lib t KKw "inl" <> sp <> sub lib 9 a
  TInr a ->
    paren (prec > 8) $ opGlyph heavy lib t KKw "inr" <> sp <> sub lib 9 a
  TApply f a ->
    paren (prec > 8) $ sub lib 8 f <> sp <> sub lib 9 a
  TSpread p x y body ->
    paren (prec > 0) $
      opGlyph heavy lib t KKw "let"
        <> sp
        <> punct "〈" "Spread binds the two components of a pair."
        <> sp
        <> binder x
        <> punct "," "Spread binds the two components of a pair."
        <> sp
        <> binder y
        <> sp
        <> punct "〉" "Spread binds the two components of a pair."
        <> sp
        <> tok KConn "=" "Spread: let 〈x, y〉 = p in …"
        <> sp
        <> sub lib 0 p
        <> sp
        <> tok KKw "in" "Spread: the body after eliminating the pair."
        <> sp
        <> sub lib 0 body
  TDecide d x left y right ->
    paren (prec > 0) $
      opGlyph heavy lib t KKw "decide"
        <> sp
        <> sub lib 0 d
        <> sp
        <> tok KKw "of" "Case split: decide t of inl x ⇒ … | inr y ⇒ …"
        <> sp
        <> tok KKw "inl" "Left injection case of decide."
        <> sp
        <> binder x
        <> sp
        <> tok KConn "⇒" "Maps an injection to its branch."
        <> sp
        <> sub lib 0 left
        <> sp
        <> tok KConn "|" "Separates the inl and inr branches of decide."
        <> sp
        <> tok KKw "inr" "Right injection case of decide."
        <> sp
        <> binder y
        <> sp
        <> tok KConn "⇒" "Maps an injection to its branch."
        <> sp
        <> sub lib 0 right
  TList a ->
    paren (prec > 8) $ opGlyph heavy lib t KType "List" <> sp <> sub lib 9 a
  TSet a x p ->
    opGlyph heavy lib t KType "{"
      <> sp
      <> binder x
      <> colon
      <> sub lib 0 a
      <> sp
      <> tok KConn "|" "Set comprehension: {x : A | P}."
      <> sp
      <> sub lib 0 p
      <> sp
      <> punct "}" "Set type closer."
  TIsect a x b
    | isDummyVar x ->
        paren (prec > 3) $
          sub lib 4 a <> sp <> opGlyph heavy lib t KConn "∩" <> sp <> sub lib 3 b
    | otherwise ->
        paren (prec > 0) $
          opGlyph heavy lib t KConn "⋂" <> sp <> binder x <> colon <> sub lib 8 a <> dotSp <> sub lib 0 b
  TQuotient a x y e
    | (isDummyVar x || not (occursFree x e)) && (isDummyVar y || not (occursFree y e)) ->
        paren (prec > 3) $
          sub lib 4 a <> sp <> opGlyph heavy lib t KConn "//" <> sp <> sub lib 3 e
    | otherwise ->
        paren (prec > 0) $
          punct "(" "Quotient binders (x, y) : A // E."
            <> binder x
            <> punct "," "The two variables of a quotient equality."
            <> binder y
            <> punct ")" "Quotient binders (x, y) : A // E."
            <> colon
            <> sub lib 8 a
            <> sp
            <> opGlyph heavy lib t KConn "//"
            <> sp
            <> sub lib 0 e
  TSquash a ->
    opGlyph heavy lib t KType "["
      <> sp
      <> sub lib 0 a
      <> sp
      <> punct "]" "Squash closer: [A] hides the extract of A."
  TAny v tyT ->
    paren (prec > 8) $
      opGlyph heavy lib t KKw "any" <> sp <> sub lib 9 v <> sp <> sub lib 9 tyT
  TIntEq a b th els ->
    paren (prec > 8) $
      opGlyph heavy lib t KKw "int_eq"
        <> sp
        <> sub lib 9 a
        <> sp
        <> sub lib 9 b
        <> sp
        <> sub lib 9 th
        <> sp
        <> sub lib 9 els
  TLess a b th els ->
    paren (prec > 8) $
      opGlyph heavy lib t KKw "less"
        <> sp
        <> sub lib 9 a
        <> sp
        <> sub lib 9 b
        <> sp
        <> sub lib 9 th
        <> sp
        <> sub lib 9 els
  TAtomEq a b th els ->
    paren (prec > 8) $
      opGlyph heavy lib t KKw "atom_eq"
        <> sp
        <> sub lib 9 a
        <> sp
        <> sub lib 9 b
        <> sp
        <> sub lib 9 th
        <> sp
        <> sub lib 9 els
  TListInd lst base x xs ih step ->
    paren (prec > 0) $
      opGlyph heavy lib t KKw "list_ind"
        <> sp
        <> sub lib 9 lst
        <> sp
        <> sub lib 9 base
        <> sp
        <> punct "(" "list_ind step: (x, xs, ih. t)."
        <> binder x
        <> punct "," "list_ind binds head, tail, and inductive hypothesis."
        <> sp
        <> binder xs
        <> punct "," "list_ind binds head, tail, and inductive hypothesis."
        <> sp
        <> binder ih
        <> dotSp
        <> sub lib 0 step
        <> punct ")" "list_ind step closer."
  TInd n x ih down base y jh up ->
    paren (prec > 0) $
      opGlyph heavy lib t KKw "ind"
        <> punct "(" "Integer induction: ind(n; down; base; up)."
        <> sub lib 0 n
        <> punct ";" "Integer induction clauses: down, base, up."
        <> sp
        <> binder x
        <> punct "," "Negative-direction binders of ind."
        <> sp
        <> binder ih
        <> dotSp
        <> sub lib 0 down
        <> punct ";" "Integer induction clauses: down, base, up."
        <> sp
        <> sub lib 0 base
        <> punct ";" "Integer induction clauses: down, base, up."
        <> sp
        <> binder y
        <> punct "," "Positive-direction binders of ind."
        <> sp
        <> binder jh
        <> dotSp
        <> sub lib 0 up
        <> punct ")" "Integer induction closer."
  TOp (Operator oid params) bts ->
    let name = opIdText oid
        nameH = opGlyph heavy lib t (termKind lib t) name
        pdoc
          | null params = emptyH
          | otherwise =
              punct "{" "Operator parameters."
                <> mconcat (punctuate (punct ";" "Parameter separator." <> sp) (map paramH params))
                <> punct "}" "Operator parameters."
        bdoc
          | null bts && null params = emptyH
          | otherwise =
              punct "(" "Operator subterm arguments."
                <> mconcat (punctuate (punct ";" "Argument separator." <> sp) (map (prettyBound lib) bts))
                <> punct ")" "Operator subterm arguments."
     in nameH <> pdoc <> bdoc

paramH :: Parameter -> Html
paramH = \case
  NatParam n ->
    tok KNum (T.pack (show n)) ("Natural-number parameter " <> T.pack (show n) <> ".")
  TokenParam s ->
    tok KVal ("\"" <> s <> "\"") ("Token parameter " <> T.pack (show s) <> ".")
  StringParam s ->
    tok KVal ("\"" <> s <> "\"") ("String parameter " <> T.pack (show s) <> ".")
  VarParam v ->
    tok KVar (varText v) ("Variable parameter " <> varText v <> ".")
  LevelParam l ->
    tok KNum (prettyLevel l) ("Level parameter " <> prettyLevel l <> ".")

prettyBound :: Library -> BoundTerm -> Html
prettyBound lib (BoundTerm vs t) =
  binders <> sub lib 0 t
  where
    binders
      | null vs = emptyH
      | otherwise =
          mconcat (punctuate (punct "," "Bound-variable separator." <> sp) (map binder vs)) <> dotSp

alphaHead :: Term -> Term -> Bool
alphaHead (TVar x) (TVar y) = x == y
alphaHead a b = a == b

paren :: Bool -> Html -> Html
paren True h =
  punct "(" "Grouping parentheses." <> h <> punct ")" "Grouping parentheses."
paren False h = h

sp :: Html
sp = raw " "

-- | Spaced colon in bindings: @x : A@.
colon :: Html
colon = sp <> tok KBinder ":" "Type ascription in a binder: x : A." <> sp

-- | Binder dot with a following space: @λ x. t@, @∀ x : A. B@.
dotSp :: Html
dotSp = tok KBinder "." "End of a binding prefix (λx. t, ∀x:A. B, …)." <> sp

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
          binder (hVar h) <> colon <> renderTermH lib (hType h)

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
    txt "decide " <> renderTermH lib a <> sp <> tok KConn "=" "Integer equality decided by compute." <> sp <> renderTermH lib b
  TxDecideLt a b ->
    txt "decide " <> renderTermH lib a <> sp <> tok KConn "<" "Integer comparison decided by compute." <> sp <> renderTermH lib b
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
            <> el "span" [("class", "turnstile"), ("data-kind", "goal"), ("data-note", "The sequent turnstile: hypotheses above prove the conclusion.")] (txt "⊢")
            <> sp
            <> el "span" [("class", "pnode-concl")] (sub lib 0 (seqConcl sq))
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
              ident = c : w
              cls = tokenClass (T.pack ident)
           in el "span" [("class", cls)] (txt (T.pack ident)) <> go more
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
