{-# LANGUAGE TypeFamilies #-}  -- for type equality ~

module Agda.TypeChecking.Monad.Context where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Control  ( MonadTransControl(..), liftThrough )

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.TypeChecking.Monad.Base

checkpointSubstitution :: MonadTCEnv tcm => CheckpointId -> tcm Substitution

class MonadTCEnv' m => MonadAddContext' m where
  -- | @addCtx x arg cont@ add a variable to the context.
  --
  --   Chooses an unused 'Name'.
  --
  --   Warning: Does not update module parameter substitution!
  addCtx :: Name -> Dom (ContextType m) -> m a -> m a

  -- | Add a let bound variable to the context
  addLetBinding' :: Name -> Term -> Dom Type -> m a -> m a

  -- | Update the context.
  --   Requires a substitution that transports things living in the old context
  --   to the new.
  updateContext :: Substitution -> (ContextOf m -> ContextOf m) -> m a -> m a

  withFreshName :: Range -> ArgName -> (Name -> m a) -> m a

  default addCtx
    :: (MonadAddContext' n, MonadTransControl t, t n ~ m,
        ContextType (t n) ~ ContextType n)
    => Name -> Dom (ContextType m) -> m a -> m a
  addCtx x a = liftThrough $ addCtx x a

  default addLetBinding'
    :: (MonadAddContext' n, MonadTransControl t, t n ~ m)
    => Name -> Term -> Dom Type -> m a -> m a
  addLetBinding' x u a = liftThrough $ addLetBinding' x u a

  default updateContext
    :: (MonadAddContext' n, MonadTransControl t, t n ~ m,
        ContextType (t n) ~ ContextType n)
    => Substitution -> (ContextOf m -> ContextOf m) -> m a -> m a
  updateContext sub f = liftThrough $ updateContext sub f

  default withFreshName
    :: (MonadAddContext' n, MonadTransControl t, t n ~ m)
    => Range -> ArgName -> (Name -> m a) -> m a
  withFreshName r x cont = do
    st <- liftWith $ \ run -> do
      withFreshName r x $ run . cont
    restoreT $ return st

instance MonadAddContext' m => MonadAddContext' (ReaderT r m) where
instance MonadAddContext' m => MonadAddContext' (StateT r m) where

instance MonadAddContext' TCM

type MonadAddContext m = (MonadAddContext' m, ContextType m ~ Type)
