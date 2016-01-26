{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
module Agda.Utils.Pointer.Monad where

import Agda.Utils.Pointer
import Control.Monad (liftM, ap)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import GHC.TypeLits (Symbol)


-- Composition of a Reader and a State monad
newtype MemoPtrM (f :: Symbol) p a b c = MemoPtrM {
  runMemoPtr :: p -> Map (Ptr a) (Ptr b) -> (Map (Ptr a) (Ptr b), c)
  }

-- | Run computations on pointers while preserving sharing
runWithMemoPtr :: p -> MemoPtrM f p a b c -> c
runWithMemoPtr p m = snd$ runMemoPtr m p (Map.empty)

localParamMemoPtr :: p -> MemoPtrM f p a b c -> MemoPtrM f p a b c
localParamMemoPtr p m = MemoPtrM (\_ s -> (s, runWithMemoPtr p m))

askParamMemoPtr :: MemoPtrM f p a b p
askParamMemoPtr = MemoPtrM (\p s -> (s, p))

applyFunMemoPtr :: (a -> MemoPtrM f p a b b) -> Ptr a -> MemoPtrM f p a b (Ptr b)
applyFunMemoPtr fun a = MemoPtrM (\p s ->
                              case Map.lookup a s of
                                Nothing ->
                                  let a' = derefPtr a
                                      (s',b') = runMemoPtr (fun a') p s
                                      b = newPtr b'
                                  in (Map.insert a b s', b)
                                Just b -> (s, b))
runWithReader :: p -> (p -> a) -> a
runWithReader p m = m p

localParamReader :: p -> (p -> a) -> (p -> a)
localParamReader p m = \_ -> m p

askParamReader :: p -> p
askParamReader = id

applyFunReader :: (a -> p -> b) -> Ptr a -> (p -> Ptr b)
applyFunReader fun a p = fmap (flip fun p) a

instance Functor (MemoPtrM (f :: Symbol) p a b) where
  fmap f = (>>= (return . f))

instance Applicative (MemoPtrM (f :: Symbol) p a b) where
  pure = return
  f <*> a = f >>= flip fmap a

instance Monad (MemoPtrM (f :: Symbol) p a b) where
  return a = MemoPtrM (\_ s -> (s, a))
  a >>= f = MemoPtrM (\p s ->
                         let (s',a') = runMemoPtr a p s in
                         runMemoPtr (f a') p s')

{-
class (Monad m) => MonadMemoPtr (f :: Symbol) p a b m | m f -> p a b where
  runWith    :: p -> m c -> c
  localParam :: p -> m c -> m c
  askParam   :: m p
  applyFun   :: Ptr a -> m (Ptr b)
-}
