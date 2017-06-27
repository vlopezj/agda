{-# OPTIONS -fno-full-laziness -fno-cse #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}
module MAlonzo.RTE.Cubical (
  Interval,
  primIMax,
  primIMin,
  primINeg,
  primPathApply,
  primPathPApply,
  primDepIMin,
  primIdFace,
  primIdPath,
  primIdJ,
  primSubOut,
  primGlue,
  prim_glue,
  prim_unglue,
  primFaceForall,
  primComp,
  primIsOneEmpty
  ) where

import MAlonzo.RTE
import System.IO.Unsafe (unsafePerformIO)
import Data.IORef (newIORef, atomicModifyIORef',IORef)
import Data.List

type Level = ()
type Natural = Integer

{-# NOINLINE intervalVariableCounter #-}
intervalVariableCounter :: IORef Integer
intervalVariableCounter = unsafePerformIO$ newIORef 0

{-# NOINLINE freshFromIntervalVariableCounter #-}
freshFromIntervalVariableCounter :: a -> Integer
freshFromIntervalVariableCounter = \a ->
  fst $ unsafePerformIO$ atomicModifyIORef' intervalVariableCounter (\i -> (i+1,(i,a))) 

mkInterval :: a -> Interval
mkInterval a = ILit IAtom { iAtomNeg = False
                          , iAtom    = freshFromIntervalVariableCounter a
                          }

-- Not the most efficient implementation by far
data IAtom = IAtom { iAtomNeg  :: Bool
                   , iAtom     :: Integer
                   } deriving (Eq,Ord)

data Interval = IMax Interval Interval
              | IMin Interval Interval
              | I1
              | I0
              | ILit IAtom
              | IDMin Interval (() -> Interval)
              | IDMax Interval (() -> Interval)

iNeg = go
  where
    go (ILit atom) = ILit (atom{iAtomNeg = not$ iAtomNeg atom})
    go I1 = I0
    go I0 = I1
    go (IMax a b) = IMin (go a) (go b)
    go (IMin a b) = IMax (go a) (go b)
    go (IDMax a b) = IDMin (go a) (go . b)
    go (IDMin a b) = IDMax (go a) (go . b)


type Face = Interval

primIMax :: Interval -> Interval -> Interval
primIMax = IMax

primIMin :: Interval -> Interval -> Interval
primIMin = IMin

primDepIMin :: Interval {- φ -} ->
               (() {- IsOne φ -} -> Interval) ->
               Interval
primDepIMin = IDMin

primINeg :: Interval -> Interval
primINeg = iNeg

type Path a = PathP
newtype PathP = PathP { path :: Interval -> Any }  

data Any where Any :: forall a. a -> Any

coeAny :: Any -> b
coeAny (Any a) = coe a

primPathApply :: Path a -> Interval -> a
primPathApply (PathP p) i = coeAny (p i)

primPathPApply :: PathP -> Interval -> a 
primPathPApply (PathP p) i = coeAny$ p i

data IdElem a = IdElem { constantAt :: Face
                       , idTypePath :: Path a
                       }


primIdFace :: Level -> El a -> a -> a -> IdElem a -> Interval
primIdFace _a _A _x _y = constantAt

primIdPath :: Level -> El a -> a -> a -> IdElem a -> Path a
primIdPath _a _A _x _y = idTypePath

primIdJ :: Level
           -- ^ a
        -> Level
           -- ^ p
        -> El a
           -- ^ A : Set a)
        -> a
           -- ^ x : A
        -> (a -> IdElem a -> El b)
           -- ^ (P : (y : A) (p : Id x y) -> Set p)
        -> b
           -- ^ P x (IdElem I1 (\_ -> x))
        -> a -> IdElem a -> b
primIdJ _a _l _x _P _Pxx _y _p = error "primIdJ"

type IsOne = ()

newtype Sub a = Inc { out :: a }

primSubOut :: Level -> El a -> Face -> Partial a -> Sub a -> a
primSubOut _a _A _φ u (Inc a) = error "primSubOut"

data Glue

primGlue :: Level -> Level -> El a -> Face -> (Partial a -> PartialP)
         -> PartialP -> El Glue
primGlue = error "primGlue"

prim_glue :: Level -> Level -> El a -> Face -> Partial (El b)
          -> PartialP 
          -> PartialP
          -> PartialP -> Glue
prim_glue _a _b _A _φ _T _f _pf = error "prim_glue"

prim_unglue :: Level -> Level -> El a -> Face -> Partial (El b) -> PartialP -> PartialP -> Glue -> a
prim_unglue _a _b _A _φ _T _f _pf _G = error "prim_unglue"

primFaceForall :: (Interval -> Interval) -> Interval
primFaceForall f = error "primFaceForall" {- IMax (f I0) (f I1)? -}
        
newtype Partial a = Partial { partial :: [(Interval,a)] }

type PartialP = Partial Any
 

data El a where
  El :: () -> El a

primComp :: (Interval -> El a) {- A -} ->
            Interval {- φ -} -> 
            (Interval {- i -} -> Partial a {- Partial (A i) φ -}) ->
            b {- A i0 -} ->
            c {- A i1 -}
primComp a φ p a0 =
  let !i = mkInterval a in
  case a i of
    El () -> coe a0 

primIsOneEmpty :: IsOne {- IsOne 0 -} -> a
primIsOneEmpty _ = error "isOneEmpty"

  
   

