{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Functions for abstracting terms over other terms.
module Agda.TypeChecking.Abstract (abstractTerm, piAbstract) where

import Control.Monad
import Data.Function

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad.Builtin (equalityUnview)
import Agda.TypeChecking.Substitute (mkPi, raise, raiseS, Subst(..), applySubst,
                                     applySubstNoSharing, liftS)

import Agda.Utils.Functor

#include "undefined.h"
import Agda.Utils.Impossible

import Agda.Utils.List (splitExactlyAt)

import Agda.Utils.Pointer.Monad

-- | @piAbstractTerm v a b[v] = (w : a) -> b[w]@
piAbstractTermM :: (MonadAbstractTerm m) => Type -> Type -> m Type
piAbstractTermM a b = mkPi (defaultDom ("w", a)) <$> abstractTermM b

piAbstractTermM' :: (MonadAbstractTerm m) => Term -> Type -> Type -> m Type
piAbstractTermM' v a b = localParam v$ piAbstractTermM a b

-- | @piAbstract (v, a) b[v] = (w : a) -> b[w]@
--
--   For @rewrite@, it does something special:
--
--   @piAbstract (prf, Eq a v v') b[v,prf] = (w : a) (w' : Eq a w v') -> b[w,w']@

piAbstractM :: (MonadAbstractTerm m) => (Term, EqualityView) -> Type -> m Type
piAbstractM (v, OtherType a) b = piAbstractTermM' v a b
piAbstractM (prf, eqt@(EqualityType s _ _ a v _)) b =
  funType (El s $ unArg a) . funType eqt' <$>
    (swap01 =<< abstractTermM' (unArg $ raise 1 v) =<< abstractTermM' prf b)
  where
    funType a = mkPi $ defaultDom ("w", a)
    -- Abstract the lhs (@a@) of the equality only.
    eqt1 = raise 1 eqt
    eqt' = equalityUnview $ eqt1 { eqtLhs = eqtLhs eqt1 $> var 0 }

piAbstract :: (Term, EqualityView) -> Type -> Type
piAbstract v a = runWith __IMPOSSIBLE__ $ (piAbstractM v a :: AbstractTermM Type)

abstractTermM' :: (MonadAbstractTerm m, AbstractTerm m a) => Term -> a -> m a
abstractTermM' t a = localParam t$ abstractTermM a

-- | @isPrefixOf u v = Just es@ if @v == u `applyE` es@.
class IsPrefixOf a where
  isPrefixOf :: a -> a -> Maybe Elims

instance IsPrefixOf Elims where
  isPrefixOf us vs = do
    (vs1, vs2) <- splitExactlyAt (length us) vs
    guard $ us == vs1
    return vs2

instance IsPrefixOf Args where
  isPrefixOf us vs = do
    (vs1, vs2) <- splitExactlyAt (length us) vs
    guard $ us == vs1
    return $ map Apply vs2

instance IsPrefixOf Term where
  isPrefixOf u v =
    case (ignoreSharing u, ignoreSharing v) of
      (Var   i us, Var   j vs) | i == j  -> us `isPrefixOf` vs
      (Def   f us, Def   g vs) | f == g  -> us `isPrefixOf` vs
      (Con   c us, Con   d vs) | c == d  -> us `isPrefixOf` vs
      (MetaV x us, MetaV y vs) | x == y  -> us `isPrefixOf` vs
      (u, v) -> guard (u == v) >> return []

class AbstractTerm m a where
  -- | @runWith u substM . runWith u abstractTermM == id@
  abstractTermM :: a -> m a

--type MonadAbstractTerm = MonadMemoPtr "abstractTerm" Term Term Term
type AbstractTermM = MemoPtrM "Agda.TypeChecking.Abstract.abstractTerm" Term Term Term
class Monad m => MonadAbstractTerm m where
  runWith    :: Term -> m c -> c
  localParam :: Term -> m c -> m c
  askParam   :: m Term
  applyFun   :: Ptr Term -> m (Ptr Term)
  applySubst_ :: (Subst Term a) => (Substitution' Term) -> a -> m a

instance MonadAbstractTerm AbstractTermM where
  runWith = runWithMemoPtr
  localParam = localParamMemoPtr
  askParam = askParamMemoPtr
  applyFun = applyFunMemoPtr abstractTermM
  applySubst_ s = return . applySubst s

instance MonadAbstractTerm ((->) Term) where
  runWith = runWithReader
  localParam = localParamReader
  askParam = askParamReader
  applyFun = applyFunReader abstractTermM
  applySubst_ s = return . applySubstNoSharing s

instance (MonadAbstractTerm m) => AbstractTerm m Term where
  abstractTermM v = (askParam :: m Term) >>= \case
    u | Just es <- u `isPrefixOf` v -> Var 0 <$> absT es
      | otherwise                   -> case v of
-- Andreas, 2013-10-20: the original impl. works only at base types
--    v | u == v  -> Var 0 []  -- incomplete see succeed/WithOfFunctionType
      Var i vs    -> Var (i + 1) <$> absT vs
      Lam h b     -> Lam h <$> absT b
      Def c vs    -> Def c <$> absT vs
      Con c vs    -> Con c <$> absT vs
      Pi a b      -> uncurry Pi <$> absT (a, b)
      Lit l       -> pure$ Lit l
      Level l     -> Level <$> absT l
      Sort s      -> Sort <$> absT s
      MetaV m vs  -> MetaV m <$> absT vs
      DontCare mv -> DontCare <$> absT mv
      Shared p    -> Shared <$> absT p
      where
        absT x = abstractTermM x

instance (MonadAbstractTerm m) => AbstractTerm m (Ptr Term) where
  abstractTermM = applyFun

instance (MonadAbstractTerm m) => AbstractTerm m Type where
  abstractTermM (El s v) = El <$> abstractTermM s <*> abstractTermM v

instance (MonadAbstractTerm m) => AbstractTerm m Sort where
  abstractTermM s = case s of
    Type n     -> Type <$> absS n
    Prop       -> pure Prop
    Inf        -> pure Inf
    SizeUniv   -> pure SizeUniv
    DLub s1 s2 -> DLub <$> absS s1 <*> absS s2
    where absS x = abstractTermM x

instance (MonadAbstractTerm m) => AbstractTerm m Level where
  abstractTermM (Max as) = Max <$> abstractTermM as

instance (MonadAbstractTerm m) => AbstractTerm m PlusLevel where
  abstractTermM l@ClosedLevel{} = pure l
  abstractTermM (Plus n l) = Plus n <$> abstractTermM l

instance (MonadAbstractTerm m) => AbstractTerm m LevelAtom where
  abstractTermM l = case l of
    MetaLevel m vs   -> MetaLevel m    <$> abstractTermM vs
    NeutralLevel r v -> NeutralLevel r <$> abstractTermM v
    BlockedLevel _ v -> UnreducedLevel <$> abstractTermM v -- abstracting might remove the blockage
    UnreducedLevel v -> UnreducedLevel <$> abstractTermM v

instance (MonadAbstractTerm m, AbstractTerm m a) => AbstractTerm m (Elim' a) where
  abstractTermM = traverse abstractTermM

instance (MonadAbstractTerm m, AbstractTerm m a) => AbstractTerm m (Arg a) where
  abstractTermM = traverse abstractTermM

instance (MonadAbstractTerm m, AbstractTerm m a) => AbstractTerm m (Dom a) where
  abstractTermM = traverse abstractTermM

instance (MonadAbstractTerm m, AbstractTerm m a) => AbstractTerm m [a] where
  abstractTermM = traverse abstractTermM

instance (MonadAbstractTerm m, AbstractTerm m a) => AbstractTerm m (Maybe a) where
  abstractTermM = traverse abstractTermM

instance (MonadAbstractTerm m, Subst Term a, AbstractTerm m a) => AbstractTerm m (Abs a) where
  abstractTermM (NoAbs x v) = NoAbs x <$> abstractTermM v
  abstractTermM (Abs   x v) = askParam >>= \u -> Abs x <$> (swap01 =<< localParam (raise 1 u) (abstractTermM v))

instance (MonadAbstractTerm m, AbstractTerm m a, AbstractTerm m b) => AbstractTerm m (a, b) where
  abstractTermM (x, y) = (,) <$> abstractTermM x <*> abstractTermM y

-- | This swaps @var 0@ and @var 1@.
swap01 :: (MonadAbstractTerm m, Subst Term a) => a -> m a
swap01 = applySubst_ $ var 1 :# liftS 1 (raiseS 1)

abstractTerm :: forall a. (AbstractTerm AbstractTermM a) => Term -> a -> a
abstractTerm u v = runWith u (abstractTermM v :: AbstractTermM a)

abstractTermPure :: forall a. (AbstractTerm ((->) Term) a) => Term -> a -> a
abstractTermPure u v = runWith u (abstractTermM v :: Term -> a)
