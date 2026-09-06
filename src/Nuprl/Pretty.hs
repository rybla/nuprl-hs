-- | Pretty-printing of terms, sequents, proofs, and library objects.
--
-- Surface notation is designed to round-trip through 'Nuprl.Parse' when
-- printed at precedence 0. Unicode connectives are used by default; ASCII
-- alternatives are accepted by the parser.
module Nuprl.Pretty
  ( -- * Rendering
    renderTerm
  , renderTermWidth
  , prettyTerm
  , prettyTermPrec
    -- * Sequents and proofs (re-exported convenience)
  , docToText
  ) where

import Data.Text (Text)
import Prettyprinter
import Prettyprinter.Render.Text (renderStrict)

import Nuprl.Term

--------------------------------------------------------------------------------
-- Rendering
--------------------------------------------------------------------------------

-- | Pretty-print a term with a generous default width.
renderTerm :: Term -> Text
renderTerm = renderTermWidth 80

renderTermWidth :: Int -> Term -> Text
renderTermWidth w t =
  renderStrict (layoutPretty (LayoutOptions (AvailablePerLine w 1.0)) (prettyTerm t))

docToText :: Doc ann -> Text
docToText = renderStrict . layoutPretty (LayoutOptions (AvailablePerLine 80 1.0))

prettyTerm :: Term -> Doc ann
prettyTerm = prettyTermPrec 0

--------------------------------------------------------------------------------
-- Precedence
--
--  0  λ, ∀, ∃, let
--  1  ⇒  (right)
--  2  ∨  (right)
--  3  ∧  (right)
--  4  = ∈, ∈
--  5  +, -  (left)
--  6  *, /  (left)
--  7  ::    (right)
--  8  juxtaposition (left)
--  9  atoms
--------------------------------------------------------------------------------

prettyTermPrec :: Int -> Term -> Doc ann
prettyTermPrec prec t = case t of
  TVar v -> prettyVar v
  TUniverse l -> "U{" <> pretty (prettyLevel l) <> "}"
  TProp l -> "P{" <> pretty (prettyLevel l) <> "}"
  TVoid -> "Void"
  TUnit -> "Unit"
  TAxiom -> "Ax"
  TInt -> "Int"
  TAtom -> "Atom"
  TTrue -> "True"
  TFalse -> "False"
  TNat n -> pretty n
  TToken s -> dquotes (pretty s)
  TNil -> "[]"
  TLambda x b ->
    paren (prec > 0) $
      "λ" <> prettyVar x <> "." <+> prettyTermPrec 0 b
  TAll a x b ->
    paren (prec > 0) $
      "∀" <> prettyVar x <> ":" <> prettyTermPrec 8 a <> "." <+> prettyTermPrec 0 b
  TExists a x b ->
    paren (prec > 0) $
      "∃" <> prettyVar x <> ":" <> prettyTermPrec 8 a <> "." <+> prettyTermPrec 0 b
  TNot a ->
    paren (prec > 8) $
      "¬" <> prettyTermPrec 8 a
  TImplies a b ->
    paren (prec > 1) $
      prettyTermPrec 2 a <+> "⇒" <+> prettyTermPrec 1 b
  TOr a b ->
    paren (prec > 2) $
      prettyTermPrec 3 a <+> "∨" <+> prettyTermPrec 2 b
  TLt a b ->
    paren (prec > 4) $
      prettyTermPrec 5 a <+> "<" <+> prettyTermPrec 5 b
  TAnd a b ->
    paren (prec > 3) $
      prettyTermPrec 4 a <+> "∧" <+> prettyTermPrec 3 b
  TIff a b ->
    paren (prec > 1) $
      prettyTermPrec 2 a <+> "⇔" <+> prettyTermPrec 2 b
  TFunction a x b
    | isDummyVar x || not (occursIn x b) ->
        paren (prec > 1) $
          prettyTermPrec 2 a <+> "→" <+> prettyTermPrec 1 b
    | otherwise ->
        paren (prec > 1) $
          parens (prettyVar x <> ":" <> prettyTermPrec 0 a) <+> "→" <+> prettyTermPrec 1 b
  TProduct a x b
    | isDummyVar x || not (occursIn x b) ->
        paren (prec > 3) $
          prettyTermPrec 4 a <+> "×" <+> prettyTermPrec 3 b
    | otherwise ->
        paren (prec > 3) $
          parens (prettyVar x <> ":" <> prettyTermPrec 0 a) <+> "×" <+> prettyTermPrec 3 b
  TUnion a b ->
    paren (prec > 2) $
      prettyTermPrec 3 a <+> "⊎" <+> prettyTermPrec 2 b
  TEqual ty a b
    | alphaHead a b ->
        prettyTermPrec 8 a <+> "∈" <+> prettyTermPrec 5 ty
    | otherwise ->
        paren (prec > 4) $
          prettyTermPrec 5 a <+> "=" <+> prettyTermPrec 5 b <+> "∈" <+> prettyTermPrec 5 ty
  TMember tm ty ->
    prettyTermPrec 8 tm <+> "∈" <+> prettyTermPrec 5 ty
  TAdd a b ->
    paren (prec > 5) $
      prettyTermPrec 5 a <+> "+" <+> prettyTermPrec 6 b
  TSub a b ->
    paren (prec > 5) $
      prettyTermPrec 5 a <+> "-" <+> prettyTermPrec 6 b
  TMul a b ->
    paren (prec > 6) $
      prettyTermPrec 6 a <+> "*" <+> prettyTermPrec 7 b
  TDiv a b ->
    paren (prec > 6) $
      prettyTermPrec 6 a <+> "/" <+> prettyTermPrec 7 b
  TRem a b ->
    paren (prec > 6) $
      prettyTermPrec 6 a <+> "%" <+> prettyTermPrec 7 b
  TMinus a ->
    paren (prec > 8) $
      "-" <> prettyTermPrec 8 a
  TCons h tl ->
    paren (prec > 7) $
      prettyTermPrec 8 h <+> "::" <+> prettyTermPrec 7 tl
  TPair a b ->
    angleBrackets (prettyTermPrec 0 a <> comma <+> prettyTermPrec 0 b)
  TInl a ->
    paren (prec > 8) $
      "inl" <+> prettyTermPrec 9 a
  TInr a ->
    paren (prec > 8) $
      "inr" <+> prettyTermPrec 9 a
  TApply f a ->
    paren (prec > 8) $
      prettyTermPrec 8 f <+> prettyTermPrec 9 a
  TSpread p x y body ->
    paren (prec > 0) $
      "let"
        <+> angleBrackets (prettyVar x <> comma <+> prettyVar y)
        <+> "="
        <+> prettyTermPrec 0 p
        <+> "in"
        <+> prettyTermPrec 0 body
  TDecide d x left y right ->
    paren (prec > 0) $
      "decide"
        <+> prettyTermPrec 0 d
        <+> "of"
        <+> "inl"
        <+> prettyVar x
        <+> "=>"
        <+> prettyTermPrec 0 left
        <+> "|"
        <+> "inr"
        <+> prettyVar y
        <+> "=>"
        <+> prettyTermPrec 0 right
  TList a ->
    paren (prec > 8) $
      "List" <+> prettyTermPrec 9 a
  TSet a x p ->
    braces (prettyVar x <> ":" <> prettyTermPrec 0 a <+> "|" <+> prettyTermPrec 0 p)
  TIsect a x b
    | isDummyVar x ->
        paren (prec > 3) $
          prettyTermPrec 4 a <+> "∩" <+> prettyTermPrec 3 b
    | otherwise ->
        paren (prec > 0) $
          "⋂" <> prettyVar x <> ":" <> prettyTermPrec 8 a <> "." <+> prettyTermPrec 0 b
  TSquash a ->
    brackets (prettyTermPrec 0 a)
  TAny v ty ->
    paren (prec > 8) $
      "any" <+> prettyTermPrec 9 v <+> prettyTermPrec 9 ty
  TIntEq a b th el ->
    paren (prec > 8) $
      "int_eq" <+> prettyTermPrec 9 a <+> prettyTermPrec 9 b
        <+> prettyTermPrec 9 th
        <+> prettyTermPrec 9 el
  TLess a b th el ->
    paren (prec > 8) $
      "less" <+> prettyTermPrec 9 a <+> prettyTermPrec 9 b
        <+> prettyTermPrec 9 th
        <+> prettyTermPrec 9 el
  TAtomEq a b th el ->
    paren (prec > 8) $
      "atom_eq" <+> prettyTermPrec 9 a <+> prettyTermPrec 9 b
        <+> prettyTermPrec 9 th
        <+> prettyTermPrec 9 el
  TListInd lst base x xs ih step ->
    paren (prec > 0) $
      "list_ind"
        <+> prettyTermPrec 9 lst
        <+> prettyTermPrec 9 base
        <+> parens (prettyVar x <> comma <> prettyVar xs <> comma <> prettyVar ih <> "." <+> prettyTermPrec 0 step)
  TOp (Operator oid params) bts ->
    pretty (opIdText oid) <> paramsDoc <> parens btsDoc
    where
      paramsDoc
        | null params = mempty
        | otherwise =
            braces (hsep (punctuate semi (map prettyParam params)))
      btsDoc = hsep (punctuate semi (map prettyBound bts))

prettyVar :: Var -> Doc ann
prettyVar v
  | isDummyVar v = "_"
  | otherwise = pretty (varText v)

prettyParam :: Parameter -> Doc ann
prettyParam = \case
  NatParam n -> pretty n
  TokenParam s -> dquotes (pretty s)
  StringParam s -> dquotes (pretty s)
  VarParam v -> prettyVar v
  LevelParam l -> pretty (prettyLevel l)

prettyBound :: BoundTerm -> Doc ann
prettyBound (BoundTerm vs t) =
  binders <> prettyTermPrec 0 t
  where
    binders
      | null vs = mempty
      | otherwise = hcat (punctuate comma (map prettyVar vs)) <> "."

paren :: Bool -> Doc ann -> Doc ann
paren True d = parens d
paren False d = d

angleBrackets :: Doc ann -> Doc ann
angleBrackets d = "<" <> d <> ">"

occursIn :: Var -> Term -> Bool
occursIn v (TVar x) = v == x
occursIn v (TOp _ bts) = any (\(BoundTerm vs t) -> v `notElem` vs && occursIn v t) bts

-- | Structural equality of heads used to decide "print as membership".
alphaHead :: Term -> Term -> Bool
alphaHead (TVar x) (TVar y) = x == y
alphaHead a b = a == b
