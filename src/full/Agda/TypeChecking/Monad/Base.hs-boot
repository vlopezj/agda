{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies   #-}

module Agda.TypeChecking.Monad.Base where

import Control.Monad.IO.Class (MonadIO)
import Data.Data (Data)
import Data.IORef (IORef)
import Data.Map (Map)

import Agda.Syntax.Common (Nat)
import Agda.Syntax.Concrete.Name (TopLevelModuleName)
import Agda.Syntax.Internal (Term)

import Agda.Utils.FileName (AbsolutePath)
import Agda.Utils.Pretty (Pretty)

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

data TCEnv
data TCState
newtype TCMT m a = TCM { unTCM :: IORef TCState -> TCEnv -> m a }

instance MonadIO m => Applicative (TCMT m)
instance MonadIO m => Functor (TCMT m)
instance MonadIO m => Monad (TCMT m)
instance MonadIO m => MonadIO (TCMT m)

type TCM = TCMT IO

type ModuleToSource = Map TopLevelModuleName AbsolutePath

type BackendName = String

data Comparison

newtype ProblemId = ProblemId Nat
instance Show ProblemId
instance Data ProblemId
instance Pretty ProblemId

data Polarity
