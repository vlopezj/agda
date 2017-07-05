{-# OPTIONS -fno-full-laziness -fno-cse #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
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
  primIsOneEmpty,
  El(..)
  ) where

import MAlonzo.RTE
import System.IO.Unsafe (unsafePerformIO)
import Data.IORef (newIORef, atomicModifyIORef',IORef)
import Data.Monoid ((<>))
import Control.Applicative ((<$>), (<*>), (<|>))

type Level = ()
type Natural = Integer

{-# NOINLINE intervalVariableCounter #-}
intervalVariableCounter :: IORef Integer
intervalVariableCounter = unsafePerformIO$ newIORef 0

{-# NOINLINE freshFromIntervalVariableCounter #-}
freshFromIntervalVariableCounter :: a -> Integer
freshFromIntervalVariableCounter = \a ->
  fst $ unsafePerformIO$ atomicModifyIORef' intervalVariableCounter (\i -> (i+1,(i,a))) 

mkIAtom :: a
           -- ^ Irrelevant argument. Use to avoid common subexpression elimination (CSE)
           -> IAtom
mkIAtom a = IAtom (freshFromIntervalVariableCounter a)

-- Not the most efficient implementation by far
data IAtom = IAtom Integer deriving (Eq,Ord)

data Interval = IMax Interval Interval
              | IMin Interval Interval
              | IDMin Interval (IsOne -> Interval)
                -- ^ This constructor may be redundant
              | I1
              | I0
              | ILit IAtom
              | INeg Interval

type Face = Interval

primIMax :: Interval -> Interval -> Interval
primIMax = IMax

primIMin :: Interval -> Interval -> Interval
primIMin = IMin

primDepIMin :: Interval {- φ -} ->
               (IsOne {- IsOne φ -} -> Interval) ->
               Interval
primDepIMin a f = IDMin a f

primINeg :: Interval -> Interval
primINeg = INeg 

newtype IsOne = IsOne () deriving (Monoid)

isOne :: {- φ : -} Face -> Maybe (IsOne {- φ -})
isOne I1           = Just (IsOne ())
isOne I0           = Nothing
isOne (IMin a b)   = (<>) <$> isOne a <*> isOne b
isOne (IMax a b)   = isOne a <|> isOne b
isOne (IDMin a b)  = isOne a >>= isZero . b
isOne (INeg i)     = isZero i 
isOne (ILit{})     = Nothing

isZero :: {- φ : -} Face -> Maybe (IsOne {- ~φ -})
isZero I0           = Just (IsOne ())
isZero I1           = Nothing
isZero (IMax a b)   = (<>) <$> isZero a <*> isZero b
isZero (IMin a b)   = isZero a <|> isZero b
isZero (IDMin a b)  = isZero a <|> (isOne a >>= isZero . b)
isZero (INeg i)     = isOne i 
isZero (ILit{})     = Nothing

type Path a = PathP
newtype PathP = PathP { path :: Interval -> Any }  

newtype Any = Any { unAny :: forall a. a }

mkAny :: a -> Any
mkAny a = Any (coe a)

coeAny :: Any -> b
coeAny (Any a) = a

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
           -- ^ A : Set a
        -> a
           -- ^ x : A
        -> (a -> IdElem a -> El b)
           -- ^ (P : (y : A) (p : Id x y) -> Set p)
        -> b
           -- ^ P x (IdElem I1 (\_ -> x))
        -> a -> IdElem a -> b
primIdJ _a _l _x _P _Pxx _y _p = error "primIdJ"

newtype Sub a = Inc { out :: a }

primSubOut :: Level -> El a -> Face -> Partial a -> Sub a -> a
primSubOut _a _A _φ _u (Inc _ia) = error "primSubOut"

primFaceForall :: (Interval -> Interval) -> Interval
primFaceForall _f = error "primFaceForall" {- IMax (f I0) (f I1)? -}
        
newtype Partial  a = Partial  (IsOne -> a)
newtype PartialP a = PartialP (IsOne -> a)

unPartial :: Partial a -> IsOne -> a
unPartial (Partial x) o = x o

unPartialP :: PartialP a -> IsOne -> a
unPartialP (PartialP x) o = x o

newtype Union a b = Union Any

pattern Unl :: a -> Union a b
pattern Unl a <- Union (coeAny -> a) 
  where Unl a = Union (mkAny a)

pattern Unr :: b -> Union a b
pattern Unr a <- Union (coeAny -> a) 
  where Unr a = Union (mkAny a)

apUnl :: f a -> f (Union a b)
apUnl = coe

apUnr :: f b -> f (Union a b)
apUnr = coe

data Sigma a b = Sigma { sigmaFst :: a
                       , sigmaSnd :: b
                       }

newtype Equiv a b = Equiv { unEquiv :: Sigma (a -> b) (b -> Sigma a Any) }
equivLtr :: Equiv a b -> (a -> b) 
equivLtr = sigmaFst . unEquiv

equivRtl :: Equiv a b -> (b -> a) 
equivRtl = (sigmaFst .) . sigmaSnd . unEquiv

data Glue a b where
  Eglue :: El a  {- A : Set a -}
        -> Face  {- φ : I -} 
        -> Partial  (El b) {- T : Partial (Set b) φ -}
        -> PartialP (b -> a) {- f : PartialP φ (λ o → T o → A) -}
           {- The proof that it is an equivalence may be redundant … -}
        -> PartialP (Equiv a b)  {- pf : PartialP φ (λ o → isEquiv (T o) A (f o)) -}
        -> PartialP b  {- PartialP φ T -} 
        -> a  {- A -}
        -> Glue a b

type Glue' a b = Union (Glue a b) b

primGlue :: Level -> Level
         -> El a  {- A : Set a -}
         -> Face  {- φ : I -} 
         -> Partial  (El b) {- T : Partial (Set b) φ -}
         -> PartialP (b :-> a) {- f : PartialP φ (λ o → T o → A) -}
         -> PartialP (Equiv b a)  {- pf : PartialP φ (λ o → isEquiv (T o) A (f o)) -}
         -> El (Glue' a b)
primGlue _la _lb _eA (isOne -> Just o) eB _f _pf = apUnr$ unPartial eB o
primGlue _la _lb  eA φ                 eB  f  pf = apUnl$ ElGlue eA φ eB f pf

      
prim_glue :: Level -> Level {- a b -}
          -> El a  {- A : Set a -}
          -> Face  {- φ : I -} 
          -> Partial  (El b) {- T : Partial (Set b) φ -}
          -> PartialP (b -> a) {- f : PartialP φ (λ o → T o → A) -}
          -> PartialP (Equiv a b)  {- pf : PartialP φ (λ o → isEquiv (T o) A (f o)) -}
          -> PartialP b  {- PartialP φ T -} 
          -> a {- A -}
          -> Glue' a b
prim_glue _ _ _eA (isOne -> Just o) _pT _f _pf t _a  = Unr$ unPartialP t o
prim_glue _ _  eA φ                  pT  f  pf t  a  = Unl$ Eglue eA φ pT f pf t a

prim_unglue :: Level -> Level {- a b -}
            -> El a  {- A : Set a -}
            -> Face  {- φ : I -} 
            -> Partial  (El b) {- T : Partial (Set b) φ -}
            -> PartialP (b -> a) {- f : PartialP φ (λ o → T o → A) -}
            -> PartialP (Equiv a b)  {- pf : PartialP φ (λ o → isEquiv (T o) A (f o)) -}
            -> Glue' a b
            -> a 
prim_unglue _ _ _eA (isOne -> Just o) _pT  f _pf ~(Unr b)                      = unPartialP f o b
prim_unglue _ _ _eA _φ                _pT _f _pf ~(Unl (Eglue _ _ _ _ _ _ a))  = a

type Constructor = Int

data DataLens   a = DataLens {
   unpack :: a -> (Constructor, [Any])
  ,pack   :: (Constructor, [Any]) -> a
  }
 
newtype U = U (El U)
type ElTel = [[Any] -> El Any]

newtype a :-> b = Pi { getPi :: a -> b } {- Pi { getPi :: ISubst -> a -> b } -}

-- | This data type is a deep embedding of the universe.
--   TODO: The fact that we need to use a DataLens or a RecordLens is ugly.
--
--   Once we figure out what we need, we might want to do a more shallow
--   embedding of 'elComp' and 'elRename' (among others we may need).
--
--   Note that we need to be able to apply composition and renaming to
--   values of type 'El a', so a shallow embedding must still support those.
data El a where
  ElU        :: El U
  ElPi       :: El a -> (a :-> El b)  -> El (a :-> b)
  ElPath     :: (Interval -> El Any) -> Any -> Any -> El PathP
  ElData     :: DataLens a           -> [ElTel] -> El a
  ElGlue     :: El a {- A : Set a -}
             -> Face {- φ : Face -}
             -> Partial  (El b)  {- T : Partial (Set b) φ -}
             -> PartialP (b :-> a)  {- f : PartialP φ (λ o → T o → A) -}
             -> PartialP (Equiv b a)  {- pf : PartialP φ (λ o → isEquiv (T o) A (f o)) -}
             -> El (Glue a b)
  ElI        :: El Interval
  ElPartialP :: Face -> (IsOne :-> El a) -> El (PartialP a)

elRename :: El a -> IAtom -> a -> a
elRename = error "elRename"

elComp   :: forall a b c.
            El a {- A[i] : Set -}
         -> El b {- A[i0] : Set -}
         -> El c {- A[i1] : Set -}

         -> IAtom {- i -}
         -> {- φ : -} Face  
         -> Partial a {- Partial φ (A i) -}
         -> b {- A[i0/i] -}
         -> c {- A[i1/i] -}

elComp _el@(ElData DataLens{pack,unpack} tels) _el0 _el1 _i _φ _ai a0 =
  {- a ~ b ~ c -}
  let (k, _dls)  = unpack (coe (a0 :: b) :: a)
      tel        = tels !! k
  in
  case tel of
    [] -> coe (pack (k,[]) :: a) :: c
    _  -> error "not implemented: elComp Data for constructors with arguments"
elComp ElPi{} _ _ _ _ _ _   = error "not implemented: elComp Pi"
elComp ElU{} _ _ _ _ _ _    = error "not implemented: elComp U"
elComp ElGlue{} _ _ _ _ _ _ = error "not implemented: elComp Glue"
elComp ElPath{} _ _ _ _ _ _ = error "not implemented: elComp Path"
elComp ElI{} _ _ _ _ _ _    = error "elComp used on type I, which is not fibrant"
elComp ElPartialP{} _ _ _ _ _ _ = error "elComp used on Partial type, which is not fibrant"

primComp :: forall a b c.
            (Interval -> El a) {- A -} ->
            Interval {- φ -} -> 
            (Interval {- i -} -> Partial a {- Partial (A i) φ -}) ->
            b {- A i0 -} ->
            c {- A i1 -}
primComp _a _φ _p a0 =
  {- 
  let !ia = mkIAtom (a,φ,p,a0)
      i   = ILit ia
  in
  elComp (a i) (coe (a I0) :: El b) (coe (a I1) :: El c) ia φ (p i) a0
  -}
  coe (a0 :: b) :: c 

primIsOneEmpty :: IsOne {- IsOne 0 -} -> a
primIsOneEmpty _ = error "isOneEmpty"
