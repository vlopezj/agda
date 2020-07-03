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


type TCEnv = TCEnv' Type
type role TCEnv' representational
data TCEnv' ctxty
data TCState
type role TCMT' representational representational nominal
newtype TCMT' ctxty m a = TCM { unTCM :: IORef TCState -> TCEnv' ctxty -> m a }

type TCMT = TCMT' Type

instance MonadIO m => Applicative (TCMT m)
instance MonadIO m => Functor (TCMT m)
instance MonadIO m => Monad (TCMT m)
instance MonadIO m => MonadIO (TCMT m)

type TCM = TCMT IO

type ModuleToSource = Map TopLevelModuleName AbsolutePath

type BackendName = String

data Comparison
newtype ProblemId = ProblemId Nat
data Polarity

data TwinT'' b a
type TwinT' = TwinT'' Bool
