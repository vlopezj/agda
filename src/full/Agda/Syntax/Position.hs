{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}

#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE OverlappingInstances #-}
#endif

{-| Position information for syntax. Crucial for giving good error messages.
-}

module Agda.Syntax.Position
  ( -- * Positions
    Position
  , Position'(..)
  , positionInvariant
  , startPos
  , movePos
  , movePosByString
  , backupPos

    -- * Intervals
  , Interval
  , Interval'(..)
  , intervalInvariant
  , takeI
  , dropI

    -- * Ranges
  , Range
  , Range'
  , rangeInvariant
  , consecutiveAndSeparated
  , intervalsToRange
  , rangeIntervals
  , rightMargin
  , noRange
  , posToRange
  , rStart
  , rEnd
  , rangeToInterval
  , continuous
  , continuousPerLine
  , PrintRange(..)
  , HasRange(..)
  , SetRange(..)
  , KillRange(..)
  , KillRangeT
  , killRangeMap
  , killRange1, killRange2, killRange3, killRange4, killRange5, killRange6, killRange7
  , killRange8, killRange9, killRange10, killRange11, killRange12, killRange13, killRange14
  , killRange15, killRange16, killRange17, killRange18, killRange19
  , withRangeOf
  , fuseRange
  , fuseRanges
  , beginningOf
  , beginningOfFile

    -- * Tests
  , tests
  ) where

import Prelude hiding (null)

import Control.Applicative hiding (empty)
import Control.Monad

import Data.Foldable (Foldable)
import qualified Data.Foldable as Fold
import Data.Function
import Data.Int
import Data.List hiding (null)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable (Traversable)
import Data.Typeable (Typeable)
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Void

import GHC.Generics (Generic)

import Test.QuickCheck.All

import Agda.Utils.FileName hiding (tests)
import Agda.Utils.List hiding (tests)
import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.Null
import Agda.Utils.Pretty
import Agda.Utils.QuickCheck

#include "undefined.h"
import Agda.Utils.Impossible

{--------------------------------------------------------------------------
    Types and classes
 --------------------------------------------------------------------------}

-- | Represents a point in the input.
--
-- If two positions have the same 'srcFile' and 'posPos' components,
-- then the final two components should be the same as well, but since
-- this can be hard to enforce the program should not rely too much on
-- the last two components; they are mainly there to improve error
-- messages for the user.
--
-- Note the invariant which positions have to satisfy: 'positionInvariant'.
data Position' a = Pn
  { srcFile :: !a
    -- ^ File.
  , posPos  :: !Int32
    -- ^ Position, counting from 1.
  , posLine :: !Int32
    -- ^ Line number, counting from 1.
  , posCol  :: !Int32
    -- ^ Column number, counting from 1.
  }
  deriving (Typeable, Functor, Foldable, Traversable, Generic)

positionInvariant :: Position' a -> Bool
positionInvariant p =
  posPos p > 0 && posLine p > 0 && posCol p > 0

importantPart :: Position' a -> (a, Int32)
importantPart p = (srcFile p, posPos p)

instance Eq a => Eq (Position' a) where
  (==) = (==) `on` importantPart

instance Ord a => Ord (Position' a) where
  compare = compare `on` importantPart

type SrcFile = Strict.Maybe AbsolutePath

type Position = Position' SrcFile

-- | An interval. The @iEnd@ position is not included in the interval.
--
-- Note the invariant which intervals have to satisfy: 'intervalInvariant'.
data Interval' a = Interval { iStart, iEnd :: !(Position' a) }
  deriving (Typeable, Eq, Ord, Functor, Foldable, Traversable, Generic)

type Interval = Interval' SrcFile

intervalInvariant :: Ord a => Interval' a -> Bool
intervalInvariant i =
  all positionInvariant [iStart i, iEnd i]
    &&
  iStart i <= iEnd i
    &&
  srcFile (iStart i) == srcFile (iEnd i)

-- | The length of an interval.
iLength :: Interval' a -> Int32
iLength i = posPos (iEnd i) - posPos (iStart i)

-- | A range is a sequence of intervals. The intervals should be
-- consecutive and separated, and point to the same file.
--
-- Note the invariant which ranges have to satisfy: 'rangeInvariant'.
newtype Range' a = Range (Seq (Interval' a))
  deriving
    (Typeable, Eq, Ord, Functor, Foldable, Traversable, Null, Generic)

type Range = Range' SrcFile

-- | The intervals that make up the range. The intervals are
-- consecutive and separated ('consecutiveAndSeparated').
rangeIntervals :: Range' a -> [Interval' a]
rangeIntervals (Range is) = Fold.toList is

-- | Turns a list of intervals into a range.
--
-- Precondition: 'consecutiveAndSeparated'.
intervalsToRange :: [Interval' a] -> Range' a
intervalsToRange is = Range (Seq.fromList is)

-- | Are the intervals consecutive and separated, do they all point to
-- the same file, and do they satisfy the interval invariant?
consecutiveAndSeparated :: Ord a => [Interval' a] -> Bool
consecutiveAndSeparated is =
  all intervalInvariant is
    &&
  allEqual (map (srcFile . iStart) is)
    &&
  (null is
     ||
   and (zipWith (<) (map iEnd   (init is))
                    (map iStart (tail is))))

-- | Range invariant.
rangeInvariant :: Ord a => Range' a -> Bool
rangeInvariant = consecutiveAndSeparated . rangeIntervals

-- | Conflate a range to its right margin.
rightMargin :: Range -> Range
rightMargin r@(Range is) = case Seq.viewr is of
  Seq.EmptyR -> r
  _ Seq.:> i -> getRange (i { iStart = iEnd i })

-- | Wrapper to indicate that range should be printed.
newtype PrintRange a = PrintRange a
  deriving (Eq, Ord, HasRange, SetRange, KillRange)

-- | Things that have a range are instances of this class.
class HasRange t where
    getRange :: t -> Range

instance HasRange Interval where
    getRange i = intervalToRange i

instance HasRange Range where
    getRange = id

instance HasRange Bool where
    getRange _ = noRange

-- | Precondition: The ranges of the list elements must point to the
-- same file (or be empty).
instance HasRange a => HasRange [a] where
    getRange = foldr fuseRange noRange

-- | Precondition: The ranges of the tuple elements must point to the
-- same file (or be empty).
instance (HasRange a, HasRange b) => HasRange (a,b) where
    getRange = uncurry fuseRange

-- | Precondition: The ranges of the tuple elements must point to the
-- same file (or be empty).
instance (HasRange a, HasRange b, HasRange c) => HasRange (a,b,c) where
    getRange (x,y,z) = getRange (x,(y,z))

-- | Precondition: The ranges of the tuple elements must point to the
-- same file (or be empty).
instance (HasRange a, HasRange b, HasRange c, HasRange d) => HasRange (a,b,c,d) where
    getRange (x,y,z,w) = getRange (x,(y,(z,w)))

-- | Precondition: The ranges of the tuple elements must point to the
-- same file (or be empty).
instance (HasRange a, HasRange b, HasRange c, HasRange d, HasRange e) => HasRange (a,b,c,d,e) where
    getRange (x,y,z,w,v) = getRange (x,(y,(z,(w,v))))

-- | Precondition: The ranges of the tuple elements must point to the
-- same file (or be empty).
instance (HasRange a, HasRange b, HasRange c, HasRange d, HasRange e, HasRange f) => HasRange (a,b,c,d,e,f) where
    getRange (x,y,z,w,v,u) = getRange (x,(y,(z,(w,(v,u)))))

-- | Precondition: The ranges of the tuple elements must point to the
-- same file (or be empty).
instance (HasRange a, HasRange b, HasRange c, HasRange d, HasRange e, HasRange f, HasRange g) => HasRange (a,b,c,d,e,f,g) where
    getRange (x,y,z,w,v,u,t) = getRange (x,(y,(z,(w,(v,(u,t))))))

instance HasRange a => HasRange (Maybe a) where
    getRange Nothing  = noRange
    getRange (Just a) = getRange a

instance (HasRange a, HasRange b) => HasRange (Either a b) where
    getRange = either getRange getRange

-- | If it is also possible to set the range, this is the class.
--
--   Instances should satisfy @'getRange' ('setRange' r x) == r@.
class HasRange t => SetRange t where
  setRange :: Range -> t -> t

instance SetRange Range where
  setRange = const

instance SetRange a => SetRange [a] where
  setRange r = fmap $ setRange r

-- | Killing the range of an object sets all range information to 'noRange'.
class KillRange a where
  killRange :: KillRangeT a

type KillRangeT a = a -> a

-- | Remove ranges in keys and values of a map.
killRangeMap :: (KillRange k, KillRange v) => KillRangeT (Map k v)
killRangeMap = Map.mapKeysMonotonic killRange . Map.map killRange

killRange1 :: KillRange a => (a -> b) -> a -> b

killRange2 :: (KillRange a, KillRange b) => (a -> b -> c) -> a -> b -> c

killRange3 :: (KillRange a, KillRange b, KillRange c) =>
              (a -> b -> c -> d) -> a -> b -> c -> d

killRange4 :: (KillRange a, KillRange b, KillRange c, KillRange d) =>
              (a -> b -> c -> d -> e) -> a -> b -> c -> d -> e

killRange5 :: ( KillRange a, KillRange b, KillRange c, KillRange d
              , KillRange e ) =>
              (a -> b -> c -> d -> e -> f) -> a -> b -> c -> d -> e -> f

killRange6 :: ( KillRange a, KillRange b, KillRange c, KillRange d
              , KillRange e, KillRange f ) =>
              (a -> b -> c -> d -> e -> f -> g) -> a -> b -> c -> d -> e -> f -> g

killRange7 :: ( KillRange a, KillRange b, KillRange c, KillRange d
              , KillRange e, KillRange f, KillRange g ) =>
              (a -> b -> c -> d -> e -> f -> g -> h) -> a -> b -> c -> d -> e -> f -> g -> h

killRange8 :: ( KillRange a, KillRange b, KillRange c, KillRange d
              , KillRange e, KillRange f, KillRange g, KillRange h ) =>
              (a -> b -> c -> d -> e -> f -> g -> h -> i) ->
              a -> b -> c -> d -> e -> f -> g -> h -> i

killRange9 :: ( KillRange a, KillRange b, KillRange c, KillRange d
              , KillRange e, KillRange f, KillRange g, KillRange h
              , KillRange i ) =>
              (a -> b -> c -> d -> e -> f -> g -> h -> i -> j) ->
              a -> b -> c -> d -> e -> f -> g -> h -> i -> j

killRange10 :: ( KillRange a, KillRange b, KillRange c, KillRange d
               , KillRange e, KillRange f, KillRange g, KillRange h
               , KillRange i, KillRange j ) =>
               (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k) ->
               a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k

killRange11 :: ( KillRange a, KillRange b, KillRange c, KillRange d
               , KillRange e, KillRange f, KillRange g, KillRange h
               , KillRange i, KillRange j, KillRange k ) =>
               (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l) ->
               a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l

killRange12 :: ( KillRange a, KillRange b, KillRange c, KillRange d
               , KillRange e, KillRange f, KillRange g, KillRange h
               , KillRange i, KillRange j, KillRange k, KillRange l ) =>
               (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m) ->
               a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m

killRange13 :: ( KillRange a, KillRange b, KillRange c, KillRange d
               , KillRange e, KillRange f, KillRange g, KillRange h
               , KillRange i, KillRange j, KillRange k, KillRange l
               , KillRange m ) =>
               (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m -> n) ->
               a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m -> n

killRange14 :: ( KillRange a, KillRange b, KillRange c, KillRange d
               , KillRange e, KillRange f, KillRange g, KillRange h
               , KillRange i, KillRange j, KillRange k, KillRange l
               , KillRange m, KillRange n ) =>
               (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m -> n -> o) ->
               a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m -> n -> o

killRange15 :: ( KillRange a, KillRange b, KillRange c, KillRange d
               , KillRange e, KillRange f, KillRange g, KillRange h
               , KillRange i, KillRange j, KillRange k, KillRange l
               , KillRange m, KillRange n, KillRange o ) =>
               (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m -> n -> o -> p) ->
               a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m -> n -> o -> p

killRange16 :: ( KillRange a, KillRange b, KillRange c, KillRange d
               , KillRange e, KillRange f, KillRange g, KillRange h
               , KillRange i, KillRange j, KillRange k, KillRange l
               , KillRange m, KillRange n, KillRange o, KillRange p ) =>
               (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m -> n -> o -> p -> q) ->
               a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m -> n -> o -> p -> q

killRange17 :: ( KillRange a, KillRange b, KillRange c, KillRange d
               , KillRange e, KillRange f, KillRange g, KillRange h
               , KillRange i, KillRange j, KillRange k, KillRange l
               , KillRange m, KillRange n, KillRange o, KillRange p
               , KillRange q ) =>
               (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m -> n -> o -> p -> q -> r) ->
               a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m -> n -> o -> p -> q -> r

killRange18 :: ( KillRange a, KillRange b, KillRange c, KillRange d
               , KillRange e, KillRange f, KillRange g, KillRange h
               , KillRange i, KillRange j, KillRange k, KillRange l
               , KillRange m, KillRange n, KillRange o, KillRange p
               , KillRange q, KillRange r ) =>
               (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m -> n -> o -> p -> q -> r -> s) ->
               a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m -> n -> o -> p -> q -> r -> s

killRange19 :: ( KillRange a, KillRange b, KillRange c, KillRange d
               , KillRange e, KillRange f, KillRange g, KillRange h
               , KillRange i, KillRange j, KillRange k, KillRange l
               , KillRange m, KillRange n, KillRange o, KillRange p
               , KillRange q, KillRange r, KillRange s ) =>
               (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m -> n -> o -> p -> q -> r -> s -> t) ->
               a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m -> n -> o -> p -> q -> r -> s -> t

killRange1  f a = f (killRange a)
killRange2  f a = killRange1 (f $ killRange a)
killRange3  f a = killRange2 (f $ killRange a)
killRange4  f a = killRange3 (f $ killRange a)
killRange5  f a = killRange4 (f $ killRange a)
killRange6  f a = killRange5 (f $ killRange a)
killRange7  f a = killRange6 (f $ killRange a)
killRange8  f a = killRange7 (f $ killRange a)
killRange9  f a = killRange8 (f $ killRange a)
killRange10 f a = killRange9 (f $ killRange a)
killRange11 f a = killRange10 (f $ killRange a)
killRange12 f a = killRange11 (f $ killRange a)
killRange13 f a = killRange12 (f $ killRange a)
killRange14 f a = killRange13 (f $ killRange a)
killRange15 f a = killRange14 (f $ killRange a)
killRange16 f a = killRange15 (f $ killRange a)
killRange17 f a = killRange16 (f $ killRange a)
killRange18 f a = killRange17 (f $ killRange a)
killRange19 f a = killRange18 (f $ killRange a)

instance KillRange Range where
  killRange _ = noRange

instance KillRange Void where
  killRange = id

instance KillRange () where
  killRange = id

instance KillRange Bool where
  killRange = id

instance KillRange Int where
  killRange = id

instance KillRange Integer where
  killRange = id

#if __GLASGOW_HASKELL__ >= 710
instance {-# OVERLAPPABLE #-} KillRange a => KillRange [a] where
#else
instance KillRange a => KillRange [a] where
#endif
  killRange = map killRange

-- | Overlaps with @KillRange [a]@.
#if __GLASGOW_HASKELL__ >= 710
instance {-# OVERLAPPING #-} KillRange String where
#else
instance KillRange String where
#endif
  killRange = id

#if __GLASGOW_HASKELL__ >= 710
instance {-# OVERLAPPABLE #-} KillRange a => KillRange (Map k a) where
#else
instance KillRange a => KillRange (Map k a) where
#endif
  killRange = fmap killRange

#if __GLASGOW_HASKELL__ >= 710
instance {-# OVERLAPPABLE #-} (Ord a, KillRange a) => KillRange (Set a) where
#else
instance (Ord a, KillRange a) => KillRange (Set a) where
#endif
  killRange = Set.map killRange

instance (KillRange a, KillRange b) => KillRange (a, b) where
  killRange (x, y) = (killRange x, killRange y)

instance (KillRange a, KillRange b, KillRange c) =>
         KillRange (a, b, c) where
  killRange (x, y, z) = killRange3 (,,) x y z

instance (KillRange a, KillRange b, KillRange c, KillRange d) =>
         KillRange (a, b, c, d) where
  killRange (x, y, z, u) = killRange4 (,,,) x y z u

instance KillRange a => KillRange (Maybe a) where
  killRange = fmap killRange

instance (KillRange a, KillRange b) => KillRange (Either a b) where
  killRange (Left  x) = Left  $ killRange x
  killRange (Right x) = Right $ killRange x

------------------------------------------------------------------------
-- Showing
------------------------------------------------------------------------

-- TODO: 'Show' should output Haskell-parseable representations.
-- The following instances are deprecated, and Pretty should be used
-- instead.  Later, simply derive Show for these types.

-- ASR (02 December 2014). This instance is not used anymore (module
-- the test suite) when reporting errors. See Issue 1293.
instance Show a => Show (Position' (Strict.Maybe a)) where
  show (Pn (Strict.Just f) _ l c) = show f ++ ":" ++
                                    show l ++ "," ++ show c
  show (Pn Strict.Nothing  _ l c) = show l ++ "," ++ show c

instance Show a => Show (Interval' (Strict.Maybe a)) where
  show (Interval s e) = file ++ start ++ "-" ++ end
    where
      f  = srcFile s
      sl = posLine s
      el = posLine e
      sc = posCol s
      ec = posCol e

      file :: String
      file = case f of
               Strict.Nothing -> ""
               Strict.Just f  -> show f ++ ":"

      start :: String
      start = show sl ++ "," ++ show sc

      end :: String
      end | sl == el  = show ec
          | otherwise = show el ++ "," ++ show ec

instance Show a => Show (Range' (Strict.Maybe a)) where
  show r = case rangeToInterval r of
    Nothing -> ""
    Just i  -> show i

instance Show a => Show (Range' (Maybe a)) where
  show = show . fmap Strict.toStrict

------------------------------------------------------------------------
-- Printing
------------------------------------------------------------------------

instance Pretty a => Pretty (Position' (Strict.Maybe a)) where
  pretty (Pn Strict.Nothing  _ l c) = pretty l <> pretty "," <> pretty c
  pretty (Pn (Strict.Just f) _ l c) =
    pretty f <> pretty ":" <> pretty l <> pretty "," <> pretty c

instance Pretty a => Pretty (Interval' (Strict.Maybe a)) where
  pretty (Interval s e) = file <> start <> pretty "-" <> end
    where
      f  = srcFile s
      sl = posLine s
      el = posLine e
      sc = posCol s
      ec = posCol e

      file :: Doc
      file = case f of
               Strict.Nothing -> empty
               Strict.Just f  -> pretty f <> colon

      start :: Doc
      start = pretty sl <> comma <> pretty sc

      end :: Doc
        | sl == el  = pretty ec
        | otherwise = pretty el <> comma <> pretty ec

instance Pretty a => Pretty (Range' (Strict.Maybe a)) where
  pretty r = case rangeToInterval r of
    Nothing -> empty
    Just i  -> pretty i

instance (Pretty a, HasRange a) => Pretty (PrintRange a) where
  pretty (PrintRange a) = pretty a <+> parens (text "at" <+> pretty (getRange a))

{--------------------------------------------------------------------------
    Functions on postitions and ranges
 --------------------------------------------------------------------------}

-- | The first position in a file: position 1, line 1, column 1.
startPos :: Maybe AbsolutePath -> Position
startPos f = Pn
  { srcFile = Strict.toStrict f
  , posPos  = 1
  , posLine = 1
  , posCol  = 1
  }

-- | Ranges between two unknown positions
noRange :: Range' a
noRange = Range Seq.empty

-- | Advance the position by one character.
--   A newline character (@'\n'@) moves the position to the first
--   character in the next line. Any other character moves the
--   position to the next column.
movePos :: Position' a -> Char -> Position' a
movePos (Pn f p l c) '\n' = Pn f (p + 1) (l + 1) 1
movePos (Pn f p l c) _    = Pn f (p + 1) l (c + 1)

-- | Advance the position by a string.
--
--   > movePosByString = foldl' movePos
movePosByString :: Position' a -> String -> Position' a
movePosByString = foldl' movePos

-- | Backup the position by one character.
--
-- Precondition: The character must not be @'\n'@.
backupPos :: Position' a -> Position' a
backupPos (Pn f p l c) = Pn f (p - 1) l (c - 1)

-- | Extracts the interval corresponding to the given string, assuming
-- that the string starts at the beginning of the given interval.
--
-- Precondition: The string must not be too long for the interval.
takeI :: String -> Interval' a -> Interval' a
takeI s i | genericLength s > iLength i = __IMPOSSIBLE__
          | otherwise = i { iEnd = movePosByString (iStart i) s }

-- | Removes the interval corresponding to the given string from the
-- given interval, assuming that the string starts at the beginning of
-- the interval.
--
-- Precondition: The string must not be too long for the interval.
dropI :: String -> Interval' a -> Interval' a
dropI s i | genericLength s > iLength i = __IMPOSSIBLE__
          | otherwise = i { iStart = movePosByString (iStart i) s }

-- | Converts two positions to a range.
posToRange :: Ord a => Position' a -> Position' a -> Range' a
posToRange p1 p2 | p1 < p2   = intervalToRange (Interval p1 p2)
                 | otherwise = intervalToRange (Interval p2 p1)

-- | Converts an interval to a range.
intervalToRange :: Interval' a -> Range' a
intervalToRange i = Range (Seq.singleton i)

-- | Converts a range to an interval, if possible.
rangeToInterval :: Range' a -> Maybe (Interval' a)
rangeToInterval (Range is) = case (Seq.viewl is, Seq.viewr is) of
  (head Seq.:< _, _ Seq.:> last) -> Just $
                                      Interval { iStart = iStart head
                                               , iEnd   = iEnd   last
                                               }
  _                              -> Nothing

-- | Returns the shortest continuous range containing the given one.
continuous :: Range' a -> Range' a
continuous r = case rangeToInterval r of
  Nothing -> noRange
  Just i  -> intervalToRange i

-- | Removes gaps between intervals on the same line.
continuousPerLine :: Ord a => Range' a -> Range' a
continuousPerLine r =
  Range (Seq.unfoldr step (rangeIntervals r))
  where
  step []  = Nothing
  step [i] = Just (i, [])
  step (i : is@(j : js))
    | sameLine  = step (fuseIntervals i j : js)
    | otherwise = Just (i, is)
    where
    sameLine = posLine (iEnd i) == posLine (iStart j)

-- | The initial position in the range, if any.
rStart :: Range' a -> Maybe (Position' a)
rStart r = iStart <$> rangeToInterval r

-- | The position after the final position in the range, if any.
rEnd :: Range' a -> Maybe (Position' a)
rEnd r = iEnd <$> rangeToInterval r

-- | Finds the least interval which covers the arguments.
--
-- Precondition: The intervals must point to the same file.
fuseIntervals :: Ord a => Interval' a -> Interval' a -> Interval' a
fuseIntervals x y = Interval { iStart = head ps, iEnd = last ps }
    where ps = sort [iStart x, iStart y, iEnd x, iEnd y]

-- | @fuseRanges r r'@ unions the ranges @r@ and @r'@.
--
--   Meaning it finds the least range @r0@ that covers @r@ and @r'@.
--
-- Precondition: The ranges must point to the same file (or be empty).
fuseRanges :: (Ord a) => Range' a -> Range' a -> Range' a
fuseRanges (Range is1) (Range is2) = Range (fuse is1 is2)
  where
  fuse is1 is2 = case (Seq.viewl is1, Seq.viewr is1,
                       Seq.viewl is2, Seq.viewr is2) of
    (Seq.EmptyL, _, _, _) -> is2
    (_, _, Seq.EmptyL, _) -> is1
    (s1 Seq.:< r1, l1 Seq.:> e1, s2 Seq.:< r2, l2 Seq.:> e2)
        -- Special cases.
      | iEnd e1 <  iStart s2 -> is1 Seq.>< is2
      | iEnd e2 <  iStart s1 -> is2 Seq.>< is1
      | iEnd e1 == iStart s2 -> mergeTouching l1 e1 s2 r2
      | iEnd e2 == iStart s1 -> mergeTouching l2 e2 s1 r1
        -- General cases.
      | iEnd s1 <  iStart s2 -> outputLeftPrefix s1 r1 s2 is2
      | iEnd s2 <  iStart s1 -> outputLeftPrefix s2 r2 s1 is1
      | iEnd s1 <  iEnd   s2 -> fuseSome s1 r1 s2 r2
      | otherwise            -> fuseSome s2 r2 s1 r1
    _ -> __IMPOSSIBLE__

  mergeTouching l e s r = l Seq.>< i Seq.<| r
    where
    i = Interval { iStart = iStart e, iEnd = iEnd s }

  -- The following two functions could use binary search instead of
  -- linear.

  outputLeftPrefix s1 r1 s2 is2 = s1 Seq.<| r1' Seq.>< fuse r1'' is2
    where
    (r1', r1'') = Seq.spanl (\s -> iEnd s < iStart s2) r1

  fuseSome s1 r1 s2 r2 = fuse r1' (fuseIntervals s1 s2 Seq.<| r2)
    where
    r1' = Seq.dropWhileL (\s -> iEnd s <= iEnd s2) r1

-- | Precondition: The ranges must point to the same file (or be
-- empty).
fuseRange :: (HasRange u, HasRange t) => u -> t -> Range
fuseRange x y = fuseRanges (getRange x) (getRange y)

-- | @beginningOf r@ is an empty range (a single, empty interval)
-- positioned at the beginning of @r@. If @r@ does not have a
-- beginning, then 'noRange' is returned.
beginningOf :: Range -> Range
beginningOf r = case rStart r of
  Nothing  -> noRange
  Just pos -> posToRange pos pos

-- | @beginningOfFile r@ is an empty range (a single, empty interval)
-- at the beginning of @r@'s starting position's file. If there is no
-- such position, then an empty range is returned.
beginningOfFile :: Range -> Range
beginningOfFile r = case rStart r of
  Nothing                   -> noRange
  Just (Pn { srcFile = f }) -> posToRange p p
    where p = startPos (Strict.toLazy f)

-- | @x \`withRangeOf\` y@ sets the range of @x@ to the range of @y@.
withRangeOf :: (SetRange t, HasRange u) => t -> u -> t
x `withRangeOf` y = setRange (getRange y) x

------------------------------------------------------------------------
-- Test suite

-- | The positions corresponding to the interval. The positions do not
-- refer to characters, but to the positions between characters, with
-- zero pointing to the position before the first character.
iPositions :: Interval' a -> Set Int32
iPositions i = Set.fromList [posPos (iStart i) .. posPos (iEnd i)]

-- | The positions corresponding to the range, including the
-- end-points.
rPositions :: Range' a -> Set Int32
rPositions r = Set.unions (map iPositions $ rangeIntervals r)

-- | Constructs the least interval containing all the elements in the
-- set.
makeInterval :: Set Int32 -> Set Int32
makeInterval s
  | Set.null s = Set.empty
  | otherwise  = Set.fromList [Set.findMin s .. Set.findMax s]

prop_iLength :: Interval' Integer -> Bool
prop_iLength i = iLength i >= 0

prop_startPos :: Maybe AbsolutePath -> Bool
prop_startPos = positionInvariant . startPos

prop_noRange :: Bool
prop_noRange = rangeInvariant (noRange :: Range)

prop_takeI_dropI :: Interval' Integer -> Property
prop_takeI_dropI i =
  forAll (choose (0, toInteger $ iLength i)) $ \n ->
    let s = genericReplicate n ' '
        t = takeI s i
        d = dropI s i
    in
    intervalInvariant t &&
    intervalInvariant d &&
    fuseIntervals t d == i

prop_intervalToRange :: Interval' Integer -> Bool
prop_intervalToRange i = rangeInvariant (intervalToRange i)

prop_rangeToInterval :: Range' Integer -> Bool
prop_rangeToInterval r
  | r == noRange = True
  | otherwise    =
    null r
      ||
    (intervalInvariant i &&
     iPositions i == makeInterval (rPositions r))
  where Just i = rangeToInterval r

prop_continuous :: Range -> Bool
prop_continuous r =
  rangeInvariant cr &&
  rPositions cr == makeInterval (rPositions r)
  where cr = continuous r

prop_continuousPerLine :: Range -> Bool
prop_continuousPerLine r =
  rangeInvariant r'
    &&
  distinct lineNumbers
  where
  r'@(Range is') = continuousPerLine r

  lineNumbers = Fold.concatMap lines is'
    where
    lines i | s == e    = [s]
            | otherwise = [s, e]
      where
      s = posLine (iStart i)
      e = posLine (iEnd   i)

prop_fuseIntervals :: Interval' Integer -> Property
prop_fuseIntervals i1 =
  forAll (intervalInSameFileAs i1) $ \i2 ->
    let i = fuseIntervals i1 i2 in
    intervalInvariant i &&
    iPositions i ==
      makeInterval (Set.union (iPositions i1) (iPositions i2))

prop_fuseRanges :: Range -> Property
prop_fuseRanges r1 =
  forAll (rangeInSameFileAs r1) $ \r2 ->
    let r = fuseRanges r1 r2 in
    rangeInvariant r
      &&
    rPositions r == Set.union (rPositions r1) (rPositions r2)

prop_beginningOf :: Range -> Bool
prop_beginningOf r = rangeInvariant (beginningOf r)

prop_beginningOfFile :: Range -> Bool
prop_beginningOfFile r = rangeInvariant (beginningOfFile r)

instance Arbitrary a => Arbitrary (Position' a) where
  arbitrary = do
    srcFile       <- arbitrary
    Positive pos' <- arbitrary
    let pos  = fromInteger pos'
        line = pred pos `div` 10 + 1
        col  = pred pos `mod` 10 + 1
    return (Pn {srcFile = srcFile, posPos = pos,
                posLine = line, posCol = col })

-- | Sets the 'srcFile' components of the interval.

setFile :: a -> Interval' a -> Interval' a
setFile f (Interval p1 p2) =
  Interval (p1 { srcFile = f }) (p2 { srcFile = f })

-- | Generates an interval located in the same file as the given
-- interval.

intervalInSameFileAs ::
  (Arbitrary a, Ord a) => Interval' a -> Gen (Interval' a)
intervalInSameFileAs i = setFile (srcFile $ iStart i) <$> arbitrary

prop_intervalInSameFileAs :: Interval' Integer -> Property
prop_intervalInSameFileAs i =
  forAll (intervalInSameFileAs i) $ \i' ->
    intervalInvariant i' &&
    srcFile (iStart i) == srcFile (iStart i')

-- | Generates a range located in the same file as the given
-- range.

rangeInSameFileAs :: (Arbitrary a, Ord a) => Range' a -> Gen (Range' a)
rangeInSameFileAs (Range is) = case Seq.viewl is of
  Seq.EmptyL -> arbitrary
  i Seq.:< _ -> do
    Range is <- arbitrary
    return $ Range (fmap (setFile (srcFile $ iStart i)) is)

prop_rangeInSameFileAs :: Range' Integer -> Property
prop_rangeInSameFileAs r =
  forAll (rangeInSameFileAs r) $ \r' ->
    rangeInvariant r'
      &&
    case rStart r of
      Nothing                   -> True
      Just (Pn { srcFile = f }) ->
        all ((== f) . srcFile . iStart) (rangeIntervals r')

instance (Arbitrary a, Ord a) => Arbitrary (Interval' a) where
  arbitrary = do
    (p1, p2 :: Position' a) <- liftM2 (,) arbitrary arbitrary
    let [p1', p2'] = sort [p1, p2 { srcFile = srcFile p1 }]
    return (Interval p1' p2')

instance (Ord a, Arbitrary a) => Arbitrary (Range' a) where
  arbitrary = intervalsToRange . fuse . sort . fixFiles <$> arbitrary
    where
    fixFiles []       = []
    fixFiles (i : is) = i : map (setFile $ srcFile $ iStart i) is

    fuse (i1 : i2 : is)
      | iEnd i1 >= iStart i2 = fuse (fuseIntervals i1 i2 : is)
      | otherwise            = i1 : fuse (i2 : is)
    fuse is = is

instance CoArbitrary a => CoArbitrary (Position' a)
instance CoArbitrary a => CoArbitrary (Interval' a)

instance CoArbitrary a => CoArbitrary (Range' a) where
  coarbitrary (Range is) = coarbitrary (Fold.toList is)

prop_positionInvariant :: Position' Integer -> Bool
prop_positionInvariant = positionInvariant

prop_intervalInvariant :: Interval' Integer -> Bool
prop_intervalInvariant = intervalInvariant

prop_rangeInvariant :: Range -> Bool
prop_rangeInvariant = rangeInvariant

instance Show (Position' Integer) where show = show . fmap Strict.Just
instance Show (Interval' Integer) where show = show . fmap Strict.Just
instance Show (Range'    Integer) where show = show . fmap Strict.Just

------------------------------------------------------------------------
-- * All tests
------------------------------------------------------------------------

-- Template Haskell hack to make the following $quickCheckAll work
-- under ghc-7.8.
return [] -- KEEP!

-- | Test suite.
tests :: IO Bool
tests = do
  putStrLn "Agda.Syntax.Position"
  $quickCheckAll
