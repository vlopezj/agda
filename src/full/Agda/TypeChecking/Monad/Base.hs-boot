{-# LANGUAGE CPP #-}
{-# LANGUAGE RoleAnnotations #-}
module Agda.TypeChecking.Monad.Base where

import Control.Monad.IO.Class (MonadIO)
import Data.IORef (IORef)
import Data.Map (Map)

import Agda.Syntax.Common (Nat)
import Agda.Syntax.Internal (Type)
import Agda.Syntax.Concrete.Name (TopLevelModuleName)
import Agda.Utils.FileName (AbsolutePath)

data Warning

data TCErr
data TCWarning
data NamedMeta
data HighlightingMethod
instance Show HighlightingMethod
instance Read HighlightingMethod

data HighlightingLevel
instance Show HighlightingLevel
instance Read HighlightingLevel

#if __GLASGOW_HASKELL__ < 804
type role TCEnv' nominal
type role TCMT' nominal nominal nominal
#endif
type TCEnv = TCEnv' Type
data TCEnv' ctxty
data TCState
newtype TCMT' ctxty m a = TCM { unTCM :: IORef TCState -> TCEnv' ctxty -> m a }

type TCMT = TCMT' Type

class IsContextType ctxty

instance MonadIO m => Applicative (TCMT' ctxty m)
instance MonadIO m => Functor (TCMT' ctxty m)
instance MonadIO m => Monad (TCMT' ctxty m)
instance (MonadIO m, IsContextType ctxty) => MonadIO (TCMT' ctxty m)

type TCM = TCMT IO
type TCM' ctxty = TCMT' ctxty IO

type ModuleToSource = Map TopLevelModuleName AbsolutePath

type BackendName = String

data Comparison
newtype ProblemId = ProblemId Nat
data Polarity

data TwinT'' b a
type TwinT' = TwinT'' Bool
