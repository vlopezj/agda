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
   ContextHet(.., Empty, (:<|), (:|>)),
   WithHet(..),
   twinContextAt,
   underHet,
   underHet',
   AddContextHet(..),
   SingT(..),
   mkHet_, unHet_, rHet_,
   commuteHet,
   maybeInContextHet,
   module Data.Sequence,
   SimplifyHet(..))
where

import Data.Coerce
import Data.Data (Data, Typeable)
import Data.Foldable (toList)
import Data.Sequence (Seq)
import qualified Data.Sequence as S

import Agda.Syntax.Abstract.Name
import Agda.Syntax.Concrete.Name (NameInScope(..), LensInScope(..), nameRoot, nameToRawName)
import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.Generic (TermLike(..))
import Agda.Syntax.Position

import Agda.TypeChecking.Monad.Base
import {-# SOURCE #-} Agda.TypeChecking.Conversion
import Agda.TypeChecking.Monad.Constraints
import Agda.TypeChecking.Monad.Options
import Agda.TypeChecking.Monad.Context (MonadAddContext(..), AddContext(..))
import Agda.TypeChecking.Free.Lazy (Free(freeVars'), underBinder', underBinder)

import Agda.Utils.Dependent
import Agda.Utils.Monad
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
newtype ContextHet = ContextHet { unContextHet :: Seq (Name, Dom TwinT) }
  deriving (Data, Show)

pattern Empty :: ContextHet
pattern Empty                    = ContextHet S.Empty
pattern (:<|) :: (Name, Dom TwinT) -> ContextHet -> ContextHet
pattern a :<| ctx <- ContextHet (a S.:<| (ContextHet -> ctx))
  where a :<| ctx =  ContextHet (a S.:<|  unContextHet  ctx )
pattern (:|>) :: ContextHet -> (Name, Dom TwinT) -> ContextHet
pattern ctx :|> a <- ContextHet ((ContextHet -> ctx) S.:|> a)
  where ctx :|> a =  ContextHet ( unContextHet  ctx  S.:|> a)
{-# COMPLETE Empty, (:<|) #-}
{-# COMPLETE Empty, (:|>) #-}


instance AddContextHet (Name, Dom TwinT) where
  {-# INLINABLE addContextHet #-}
  addContextHet ctx p κ = κ$ ctx :|> p

twinContextAt :: forall s. (Sing s, HetSideIsType s ~ 'True) => ContextHet -> [(Name, Dom Type)]
twinContextAt = fmap (fmap (fmap (twinAt @s))) . toList . unContextHet

instance TermLike ContextHet where
  foldTerm f = foldMap (foldTerm f . snd) . unContextHet
  traverseTermM = __IMPOSSIBLE__

instance Free ContextHet where
  freeVars' = go
    where
      go Empty          = mempty
      go ((_,v) :<| vs) = freeVars' v <> underBinder (freeVars' vs)

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

{-# INLINE mkHet_ #-}
mkHet_ :: forall s het a. (Sing het) => SingT het -> a -> If het (Het s a) a
mkHet_ _ = case sing :: SingT het of
  STrue -> Het
  SFalse -> id

unHet_ :: forall het s a. (Sing het) => If het (Het s a) a -> a
unHet_ = case sing :: SingT het of
  STrue  -> unHet
  SFalse -> id

rHet_ :: forall s het a. (Sing het) => If het (Het s a) a -> Het s a
rHet_ = case sing :: SingT het of
  STrue  -> id
  SFalse -> Het


{-# INLINE commuteHet #-}
commuteHet :: (Coercible (f a) (f (Het s a))) => Het s (f a) -> f (Het s a)
commuteHet = coerce . unHet

{-# INLINE maybeInContextHet #-}
maybeInContextHet :: (HasOptions m) =>
  SingT het -> If het ContextHet () ->
    (forall het'. (Sing het', het' ~ Or het het', het' ~ Or het' het) =>
       SingT het' -> If (Or het het') ContextHet () -> m a) -> m a
maybeInContextHet hetuni ctx κ = do
  case hetuni of
    STrue  -> κ STrue ctx
    SFalse ->
      heterogeneousUnification >>= \case
        True  -> κ STrue Empty
        False -> κ SFalse ()

class SimplifyHet a where
  type Simplified a
  unsimplifyHet :: Simplified a -> a
  simplifyHet   :: MonadConversion m => a -> (Either a (Simplified a) -> m b) -> m b

simplifyHet' :: (MonadConversion m, SimplifyHet a) => a -> (a -> m b) -> m b
simplifyHet' a κ = simplifyHet a $ \case
  Left  a' -> κ a'
  Right a' -> κ $ unsimplifyHet a'

instance SimplifyHet ContextHet where
  type Simplified ContextHet = ()

  unsimplifyHet () = Empty

  simplifyHet Empty κ = κ (Right ())
  simplifyHet ((name, dt) :<| ctx) κ =
    simplifyHet dt $ \case
      Right dt' -> addContext (name, dt') $ simplifyHet ctx κ
      Left  dt' -> κ$ Left$ ((name, dt') :<| ctx)

instance SimplifyHet TwinT where
  type Simplified TwinT = Type

  unsimplifyHet = SingleT . Het @'Both

  simplifyHet (SingleT a) κ = κ$ Right $ unHet @'Both a
  simplifyHet a@(TwinT{twinPid,twinCompat}) κ =
    allM twinPid isProblemSolved >>= \case
      True  -> κ$ Right $ unHet @'Compat twinCompat
      False -> κ$ Left  a

instance SimplifyHet a => SimplifyHet (WithHet a) where
  type Simplified (WithHet a) = Simplified a

  unsimplifyHet = WithHet Empty . unsimplifyHet

  simplifyHet (WithHet ctx a) κ = simplifyHet ctx $ \case
    Right () -> simplifyHet a $ \case
      Left  a' -> κ$ Left$ WithHet Empty a'
      Right a' -> κ$ Right$ a'
    Left ctx'  -> κ$ Left$ WithHet ctx' a

instance SimplifyHet a => SimplifyHet (Dom a) where
  type Simplified (Dom a) = Dom (Simplified a)

  unsimplifyHet = fmap unsimplifyHet
  simplifyHet a κ = simplifyHet (unDom a) $ \case
    Left  a' -> κ$ Left$  a{unDom=a'}
    Right a' -> κ$ Right$ a{unDom=a'}

instance SimplifyHet a => SimplifyHet (CompareAs' a) where
  type Simplified (CompareAs' a) = CompareAs' (Simplified a)

  unsimplifyHet = fmap unsimplifyHet
  simplifyHet AsTypes κ     = κ (Right AsTypes)
  simplifyHet AsSizes κ     = κ (Right AsSizes)
  simplifyHet (AsTermsOf a) κ = simplifyHet a $ \case
    Right a' -> κ$ Right$ AsTermsOf a'
    Left  a' -> κ$ Left$  AsTermsOf a'

instance SimplifyHet a => SimplifyHet (Het side a) where
  type Simplified (Het side a) = Simplified a

  unsimplifyHet = Het . unsimplifyHet

  simplifyHet (Het a) κ = simplifyHet a $ \case
    Right a' -> κ$ Right a'
    Left  a' -> κ$ Left$ Het a'
