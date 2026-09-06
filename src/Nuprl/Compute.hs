-- | Computation (reduction) of NuPRL terms.
--
-- The operational semantics is lazy: 'whnf' reduces to a weak-head canonical
-- form, unfolding soft logic encodings along the way. Full 'normalize' reduces
-- under binders as well.
module Nuprl.Compute
  ( step
  , whnf
  , whnfFuel
  , normalize
  , normalizeFuel
  , unfoldSoft
  , unfoldSoftOnce
  , unfoldSoftDeep
  , computeEq
  , defaultFuel
  ) where

import Nuprl.Subst
import Nuprl.Term

-- | Fuel for bounded reduction, guarding against non-termination of recursive
-- computations (none of the primitive operators are currently rec-based, but
-- user abstractions could in principle loop if we ever allowed them).
defaultFuel :: Int
defaultFuel = 10000

-- | A single weak-head reduction step. Returns 'Nothing' if the term is
-- already in weak-head normal form (or is a stuck redex).
step :: Term -> Maybe Term
step t = case unfoldSoftOnce t of
  Just t' -> Just t'
  Nothing -> stepPrimitive t

stepPrimitive :: Term -> Maybe Term
stepPrimitive = \case
  TApply f a ->
    case whnf f of
      TLambda x b -> Just (subst1 x a b)
      f' | not (alphaEq f f') -> Just (TApply f' a)
      _ -> Nothing
  TSpread p x y body ->
    case whnf p of
      TPair a b -> Just (substMany [x, y] [a, b] body)
      p' | not (alphaEq p p') -> Just (TSpread p' x y body)
      _ -> Nothing
  TDecide d x left y right ->
    case whnf d of
      TInl a -> Just (subst1 x a left)
      TInr b -> Just (subst1 y b right)
      d' | not (alphaEq d d') -> Just (TDecide d' x left y right)
      _ -> Nothing
  TMinus a ->
    case whnf a of
      TNat n -> Just (TNat (negate n))
      a' | not (alphaEq a a') -> Just (TMinus a')
      _ -> Nothing
  TAdd a b -> binInt (+) TAdd a b
  TSub a b -> binInt (-) TSub a b
  TMul a b -> binInt (*) TMul a b
  TDiv a b -> binIntNz div TDiv a b
  TRem a b -> binIntNz rem TRem a b
  TIntEq a b th el ->
    case (whnf a, whnf b) of
      (TNat n, TNat m) -> Just (if n == m then th else el)
      _ -> Nothing
  TLess a b th el ->
    case (whnf a, whnf b) of
      (TNat n, TNat m) -> Just (if n < m then th else el)
      _ -> Nothing
  TLt a b ->
    case (whnf a, whnf b) of
      (TNat n, TNat m) -> Just (if n < m then TUnit else TVoid)
      (a', b')
        | not (alphaEq a a') || not (alphaEq b b') -> Just (TLt a' b')
        | otherwise -> Nothing
  TAtomEq a b th el ->
    case (whnf a, whnf b) of
      (TToken s, TToken t) -> Just (if s == t then th else el)
      _ -> Nothing
  TListInd lst base x xs ih stepT ->
    case whnf lst of
      TNil -> Just base
      TCons h tl ->
        let rec = TListInd tl base x xs ih stepT
         in Just (substMany [x, xs, ih] [h, tl, rec] stepT)
      lst' | not (alphaEq lst lst') -> Just (TListInd lst' base x xs ih stepT)
      _ -> Nothing
  TInd n x ih down base y jh up ->
    case whnf n of
      TNat k
        | k == 0 -> Just base
        | k > 0 ->
            let rec = TInd (TNat (k - 1)) x ih down base y jh up
             in Just (substMany [y, jh] [TNat (k - 1), rec] up)
        | otherwise ->
            let rec = TInd (TNat (k + 1)) x ih down base y jh up
             in Just (substMany [x, ih] [TNat (k + 1), rec] down)
      n'
        | not (alphaEq n n') -> Just (TInd n' x ih down base y jh up)
      _ -> Nothing
  TAny v ty ->
    case whnf v of
      v' | not (alphaEq v v') -> Just (TAny v' ty)
      _ -> Nothing
  _ -> Nothing

binInt :: (Integer -> Integer -> Integer) -> (Term -> Term -> Term) -> Term -> Term -> Maybe Term
binInt f cons a b =
  case (whnf a, whnf b) of
    (TNat n, TNat m) -> Just (TNat (f n m))
    (a', b')
      | not (alphaEq a a') || not (alphaEq b b') -> Just (cons a' b')
      | otherwise -> Nothing

binIntNz :: (Integer -> Integer -> Integer) -> (Term -> Term -> Term) -> Term -> Term -> Maybe Term
binIntNz f cons a b =
  case (whnf a, whnf b) of
    (TNat _, TNat 0) -> Nothing
    (TNat n, TNat m) -> Just (TNat (f n m))
    (a', b')
      | not (alphaEq a a') || not (alphaEq b b') -> Just (cons a' b')
      | otherwise -> Nothing

-- | Weak-head normal form, with a fuel bound.
whnfFuel :: Int -> Term -> Term
whnfFuel n t
  | n <= 0 = t
  | otherwise = case step t of
      Nothing -> t
      Just t' -> whnfFuel (n - 1) t'

whnf :: Term -> Term
whnf = whnfFuel defaultFuel

-- | Reduce under binders and in all subterms.
normalizeFuel :: Int -> Term -> Term
normalizeFuel n t =
  let t' = whnfFuel n t
   in case t' of
        TVar _ -> t'
        TOp op bts -> TOp op (map (\(BoundTerm vs b) -> BoundTerm vs (normalizeFuel (n `div` 2 + 1) b)) bts)

normalize :: Term -> Term
normalize = normalizeFuel defaultFuel

--------------------------------------------------------------------------------
-- Soft encodings
--------------------------------------------------------------------------------

-- | Unfold a soft logic encoding at the root, one layer.
unfoldSoftOnce :: Term -> Maybe Term
unfoldSoftOnce = \case
  TTrue -> Just TUnit
  TFalse -> Just TVoid
  TNot a -> Just (tArrow a TVoid)
  TAnd a b -> Just (tTimes a b)
  TOr a b -> Just (TUnion a b)
  TImplies a b -> Just (tArrow a b)
  TIff a b -> Just (tTimes (tArrow a b) (tArrow b a))
  TAll a x b -> Just (TFunction a x b)
  TExists a x b -> Just (TProduct a x b)
  TMember t ty -> Just (TEqual ty t t)
  TProp l -> Just (TUniverse l)
  _ -> Nothing

-- | Unfold soft encodings at the root until a primitive remains.
unfoldSoft :: Term -> Term
unfoldSoft t = case unfoldSoftOnce t of
  Just t' -> unfoldSoft t'
  Nothing -> t

-- | Unfold soft encodings everywhere.
unfoldSoftDeep :: Term -> Term
unfoldSoftDeep t =
  let t' = unfoldSoft t
   in case t' of
        TVar _ -> t'
        TOp op bts -> TOp op (map (mapBound unfoldSoftDeep) bts)

-- | Computational equality (conversion): lazy comparison of weak-head
-- normal forms, recursively converting subterms. So @f ((λx. t) a)@
-- converts with @f (t[a/x])@ even though the outer apply is already a
-- weak-head redex.
computeEq :: Term -> Term -> Bool
computeEq a b = conv (whnf a) (whnf b)

conv :: Term -> Term -> Bool
conv a b
  | alphaEq a b = True
  | otherwise = case (a, b) of
      (TOp (Operator oid1 ps1) bts1, TOp (Operator oid2 ps2) bts2)
        | oid1 == oid2
            && ps1 == ps2
            && length bts1 == length bts2 ->
            and (zipWith convBound bts1 bts2)
      _ -> False

convBound :: BoundTerm -> BoundTerm -> Bool
convBound (BoundTerm vs1 t1) (BoundTerm vs2 t2)
  | length vs1 /= length vs2 = False
  | vs1 == vs2 = computeEq t1 t2
  | otherwise =
      computeEq t1 (substMany vs2 (map TVar vs1) t2)
