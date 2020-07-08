{-# LANGUAGE KindSignatures  #-}
{-# LANGUAGE PolyKinds       #-}
{-# LANGUAGE TypeFamilies    #-}
module Agda.Utils.Dependent where

import qualified Data.Kind as Hs

-- Poor man's
-- https://cs.brynmawr.edu/~rae/papers/2012/singletons/paper.pdf
data family SingT :: k -> Hs.Type

class Sing (a :: k) where
  sing :: SingT a
