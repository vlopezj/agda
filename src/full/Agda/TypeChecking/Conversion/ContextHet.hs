{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE TypeFamilies               #-}

module Agda.TypeChecking.Conversion.ContextHet
  (TwinT,TwinT',TwinT''(..),
   HetSideIsType,
   twinAt,
   HetSide(..),
   Het(..),
   ContextHet(..),
   WithHet(..),
   twinContextAt,
   underHet,
   underHet',
   AddContextHet(..),
   SingT(..),
   mkHet_, unHet_,
   commuteHet)
where

import Data.Data (Data, Typeable)
import Data.Coerce

import Agda.Syntax.Abstract.Name
import Agda.Syntax.Concrete.Name (NameInScope(..), LensInScope(..), nameRoot, nameToRawName)
import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.Generic (TermLike(..))
import Agda.Syntax.Position

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Context (MonadAddContext(..), AddContext(..))
import Agda.TypeChecking.Free.Lazy (Free(freeVars'), underBinder', underBinder)

import Agda.Utils.Dependent
import Agda.Utils.Pretty
import Agda.Utils.Size

import Agda.Utils.Impossible

----------------------------------------------------------------------
-- * Data structure for a twin type
----------------------------------------------------------------------

data TwinT'' b a  =
    SingleT { unSingleT :: Het 'Both a }
  | TwinT { twinPid    :: [ProblemId]      -- ^ Unification problem which is sufficient
                                           --   for LHS and RHS to be equal
          , necessary  :: b                -- ^ Whether solving twinPid is necessary,
                                           --   not only sufficient.
          , twinLHS    :: Het 'LHS a       -- ^ Left hand side of the twin
          , twinRHS    :: Het 'RHS a       -- ^ Right hand side of the twin
          , twinCompat :: Het 'Compat a    -- ^ A term which can be used instead of the
                                      --   twin for backwards compatibility
                                      --   purposes.
          }
   deriving (Foldable, Traversable)

deriving instance (Data a, Data b) => Data (TwinT'' a b)
deriving instance (Show a, Show b) => Show (TwinT'' a b)
deriving instance Functor (TwinT'' b)

type TwinT' = TwinT'' Bool

type TwinT = TwinT' Type

data WithHet a = WithHet ContextHet a

type family HetSideIsType (s :: HetSide) :: Bool where
  HetSideIsType 'LHS    = 'True
  HetSideIsType 'RHS    = 'True
  HetSideIsType 'Compat = 'True
  HetSideIsType 'Both   = 'True
  HetSideIsType 'Whole  = 'False
{-# INLINE twinAt #-}
twinAt :: forall s. (Sing s, HetSideIsType s ~ 'True) => TwinT -> Type
twinAt (SingleT a) = unHet @'Both a
twinAt TwinT{twinLHS,twinRHS,twinCompat} = case (sing :: SingT s) of
  SLHS    -> unHet @s $ twinLHS
  SBoth   -> unHet @'LHS $ twinLHS
  SRHS    -> unHet @s $ twinRHS
  SCompat -> unHet @s $ twinCompat

-- unTwinTCompat :: TwinT'' b a -> a
-- unTwinTCompat (SingleT s) = unHet @'Both s
-- unTwinTCompat (TwinT{twinCompat=s}) = unHet @'Compat s
--
-- pattern TwinTCompat :: a -> TwinT'' b a
-- pattern TwinTCompat s <- (unTwinTCompat -> s)
--   where
--     TwinTCompat s = SingleT (Het @'Both s)

-- #if __GLASGOW_HASKELL__ >= 802
-- {-# COMPLETE TwinTCompat #-}
-- #endif

-- We do not derive Traverse because we want to be careful when handling the "necessary" bit
openTwinT :: TwinT'' Bool a -> TwinT'' () a
openTwinT (SingleT a) = SingleT a
openTwinT (TwinT{twinPid,twinLHS,twinRHS,twinCompat}) =
  TwinT{twinPid,necessary=(),twinLHS,twinRHS,twinCompat}

closeTwinT :: TwinT'' () a -> TwinT'' Bool a
closeTwinT (SingleT a) = SingleT a
closeTwinT (TwinT{twinPid,twinLHS,twinRHS,twinCompat}) =
  TwinT{twinPid,necessary=False,twinLHS,twinRHS,twinCompat}


instance Free TwinT where

instance TermLike TwinT where
  traverseTermM f = \case
    SingleT a -> SingleT <$> traverseTermM f a
    TwinT{twinPid,twinLHS=a,twinRHS=b,twinCompat=c} ->
      (\a' b' c' -> TwinT{twinPid,necessary=False,twinLHS=a',twinRHS=b',twinCompat=c'}) <$>
        traverseTermM f a <*> traverseTermM f b <*> traverseTermM f c

instance Pretty a => Pretty (TwinT' a) where
  pretty (SingleT a) = pretty a
  pretty (TwinT{twinPid,necessary,twinLHS=a,twinRHS=b}) =
    pretty a <> "‡"
             <> "["
             <> pretty twinPid
             <> (if necessary then "" else "*")
             <> "]"
             <> pretty b

data HetSide = LHS | RHS | Compat | Whole | Both
data instance SingT (a :: HetSide) where
  SLHS    :: SingT 'LHS
  SRHS    :: SingT 'RHS
  SCompat :: SingT 'Compat
  SWhole  :: SingT 'Whole
  SBoth   :: SingT 'Both
instance Sing 'LHS    where sing = SLHS
instance Sing 'RHS    where sing = SRHS
instance Sing 'Both   where sing = SBoth
instance Sing 'Compat where sing = SCompat
instance Sing 'Whole  where sing = SWhole

newtype Het (side :: HetSide) t = Het { unHet :: t }
  deriving (Foldable, Traversable, Pretty)

deriving instance (Typeable side, Data t) => Data (Het side t)
deriving instance Show t => Show (Het side t)
deriving instance Functor (Het side)

instance Applicative (Het s) where
  pure = Het
  mf <*> ma = mf >>= (\f -> ma >>= (\a -> pure (f a)))
instance Monad (Het s) where
  Het a >>= f = f a

instance TermLike t => TermLike (Het a t) where

-- | The context is in left-to-right order
newtype ContextHet = ContextHet { unContextHet :: [(Name, Dom TwinT)] }
  deriving (Data, Show)

instance AddContextHet (Name, Dom TwinT) where
  {-# INLINABLE addContextHet #-}
  addContextHet (ContextHet ctx) p κ = κ$ ContextHet$ ctx ++ [p]

twinContextAt :: forall s. (Sing s, HetSideIsType s ~ 'True) => ContextHet -> [(Name, Dom Type)]
twinContextAt = fmap (fmap (fmap (twinAt @s))) . unContextHet

instance TermLike ContextHet where
  foldTerm f = go . unContextHet
    where
      go [] = mempty
      go ((_,v):vs) = foldTerm f (v, ContextHet vs)
  traverseTermM = __IMPOSSIBLE__

instance Free ContextHet where
  freeVars' = go . unContextHet
    where
      go []         = mempty
      go ((_,v):vs) = freeVars' v <> underBinder (freeVars' (ContextHet vs))

instance Sized ContextHet where
  size = length . unContextHet

-- | Various specializations of @addCtx@.
class AddContextHet b where
  addContextHet  :: (MonadTCEnv m, MonadAddContext m) =>
    ContextHet -> b -> (ContextHet -> m a) -> m a

instance AddContextHet (String, Dom TwinT) where
  {-# INLINABLE addContextHet #-}
  addContextHet ctx (s, dom) κ = do
    withFreshName noRange s $ \x ->
      addContextHet ctx (setNotInScope x, dom) κ

-- | Run under a side of a twin context
{-# SPECIALIZE underHet :: ContextHet -> (a -> TCM b) -> Het 'LHS a -> TCM (Het 'LHS b) #-}
{-# SPECIALIZE underHet :: ContextHet -> (a -> TCM b) -> Het 'RHS a -> TCM (Het 'RHS b) #-}
{-# SPECIALIZE underHet :: ContextHet -> (a -> TCM b) -> Het 'Compat a -> TCM (Het 'Compat b) #-}
underHet :: forall s m a b. (MonadAddContext m, Sing s, HetSideIsType s ~ 'True) => ContextHet -> (a -> m b) -> Het s a -> m (Het s b)
underHet ctx f = traverse (addContext (twinContextAt @s ctx) . f)

underHet' :: forall s m a het. (MonadAddContext m, Sing s, HetSideIsType s ~ 'True) =>
             SingT het -> If het ContextHet () -> m a -> m a
underHet' STrue  ctx = addContext (twinContextAt @s ctx)
underHet' SFalse ()  = id

mkHet_ :: forall het s a. (Sing het) => a -> If het (Het s a) a
mkHet_ = case sing :: SingT het of
  STrue -> Het
  SFalse -> id

unHet_ :: forall het s a. (Sing het) => If het (Het s a) a -> a
unHet_ = case sing :: SingT het of
  STrue  -> unHet
  SFalse -> id


commuteHet :: (Coercible (f a) (f (Het s a))) => Het s (f a) -> f (Het s a)
commuteHet = coerce . unHet
