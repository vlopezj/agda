{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE TypeFamilies             #-}

module Agda.TypeChecking.Reduce where

import Control.Applicative ((<|>))
import Control.Monad.Reader

import Data.Maybe
import Data.Map (Map)
import Data.Foldable
import Data.Traversable
import Data.HashMap.Strict (HashMap)
import qualified Data.Set as Set

import Agda.Interaction.Options

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.MetaVars
import Agda.Syntax.Scope.Base (Scope)
import Agda.Syntax.Literal

import {-# SOURCE #-} Agda.TypeChecking.Irrelevance (workOnTypes, isPropM)
import {-# SOURCE #-} Agda.TypeChecking.Level (reallyUnLevelView)
import Agda.TypeChecking.Conversion.ContextHet
import Agda.TypeChecking.Monad hiding ( enterClosure, constructorForm )
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.EtaContract

import Agda.TypeChecking.Reduce.Monad

import {-# SOURCE #-} Agda.TypeChecking.CompiledClause.Match
import {-# SOURCE #-} Agda.TypeChecking.Patterns.Match
import {-# SOURCE #-} Agda.TypeChecking.Pretty
import {-# SOURCE #-} Agda.TypeChecking.Rewriting
import {-# SOURCE #-} Agda.TypeChecking.Reduce.Fast

import Agda.Utils.Dependent
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.Maybe
import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.Monad
import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.Size
import Agda.Utils.Tuple
import qualified Agda.Utils.SmallSet as SmallSet

import Agda.Utils.Impossible

instantiate :: (Instantiate a, MonadReduce m) => a -> m a
instantiate = liftReduce . instantiate'

instantiateFull :: (InstantiateFull a, MonadReduce m) => a -> m a
instantiateFull = liftReduce . instantiateFull'

reduce :: (Reduce a, MonadReduce m) => a -> m a
reduce = liftReduce . reduce'

reduceB :: (Reduce a, MonadReduce m) => a -> m (Blocked a)
reduceB = liftReduce . reduceB'

normalise :: (Normalise a, MonadReduce m) => a -> m a
normalise = liftReduce . normalise'

-- | Normalise the given term but also preserve blocking tags
--   TODO: implement a more efficient version of this.
normaliseB :: (MonadReduce m, Reduce t, Normalise t) => t -> m (Blocked t)
normaliseB = normalise >=> reduceB

simplify :: (Simplify a, MonadReduce m) => a -> m a
simplify = liftReduce . simplify'

-- | Meaning no metas left in the instantiation.
isFullyInstantiatedMeta :: MetaId -> TCM Bool
isFullyInstantiatedMeta m = do
  mv <- lookupMeta m
  case mvInstantiation mv of
    InstV _tel v -> noMetas <$> instantiateFull v
    _ -> return False

-- | Blocking on all blockers.
blockAll :: (Functor f, Foldable f) => f (Blocked a) -> Blocked (f a)
blockAll bs = blockedOn block $ fmap ignoreBlocking bs
  where block = unblockOnAll $ foldMap (Set.singleton . blocker) bs
        blocker NotBlocked{}  = alwaysUnblock
        blocker (Blocked b _) = b

-- | Blocking on any blockers. Also metavariables. TODO: isMeta not needed once we could metas as
--   Blocked.
blockAny :: (IsMeta a, Functor f, Foldable f) => f (Blocked a) -> Blocked (f a)
blockAny bs = blockedOn block $ fmap ignoreBlocking bs
  where block = case foldMap blocker bs of
                  [] -> alwaysUnblock -- no blockers
                  bs -> unblockOnAny $ Set.fromList bs
        blocker (NotBlocked _ t) | Just x <- isMeta t = [unblockOnMeta x]
        blocker NotBlocked{}                          = []
        blocker (Blocked b _)                         = [b]

-- | Instantiate something.
--   Results in an open meta variable or a non meta.
--   Doesn't do any reduction, and preserves blocking tags (when blocking meta
--   is uninstantiated).
class Instantiate t where
  instantiate' :: t -> ReduceM t

  default instantiate' :: (t ~ f a, Traversable f, Instantiate a) => t -> ReduceM t
  instantiate' = traverse instantiate'

instance Instantiate t => Instantiate [t]
instance Instantiate t => Instantiate (Map k t)
instance Instantiate t => Instantiate (Maybe t)
instance Instantiate t => Instantiate (Strict.Maybe t)

instance Instantiate t => Instantiate (Abs t)
instance Instantiate t => Instantiate (Arg t)
instance Instantiate t => Instantiate (Elim' t)
instance Instantiate t => Instantiate (Tele t)

instance (Instantiate a, Instantiate b) => Instantiate (a,b) where
    instantiate' (x,y) = (,) <$> instantiate' x <*> instantiate' y

instance (Instantiate a, Instantiate b,Instantiate c) => Instantiate (a,b,c) where
    instantiate' (x,y,z) = (,,) <$> instantiate' x <*> instantiate' y <*> instantiate' z

instance Instantiate Term where
  instantiate' t@(MetaV x es) = do
    blocking <- view stInstantiateBlocking <$> getTCState

    mv <- lookupMeta x
    let mi = mvInstantiation mv

    case mi of
      InstV tel v -> instantiate' inst
        where
          -- A slight complication here is that the meta might be underapplied,
          -- in which case we have to build the lambda abstraction before
          -- applying the substitution, or overapplied in which case we need to
          -- fall back to applyE.
          (es1, es2) = splitAt (length tel) es
          vs1 = reverse $ map unArg $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es1
          rho = vs1 ++# wkS (length vs1) idS
                -- really should be .. ++# emptyS but using wkS makes it reduce to idS
                -- when applicable
          -- specification: inst == foldr mkLam v tel `applyE` es
          inst = applySubst rho (foldr mkLam v $ drop (length es1) tel) `applyE` es2
      _ | Just m' <- mvTwin mv, blocking -> do
            instantiate' (MetaV m' es)
      Open                             -> return t
      OpenInstance                     -> return t
      BlockedConst u | blocking  -> instantiate' . unBrave $ BraveTerm u `applyE` es
                     | otherwise -> return t
      PostponedTypeCheckingProblem _ _ -> return t
  instantiate' (Level l) = levelTm <$> instantiate' l
  instantiate' (Sort s) = Sort <$> instantiate' s
  instantiate' t = return t

instance Instantiate t => Instantiate (Type' t) where
  instantiate' (El s t) = El <$> instantiate' s <*> instantiate' t

instance Instantiate Level where
  instantiate' (Max m as) = levelMax m <$> instantiate' as

-- Note: since @PlusLevel' t@ embeds a @LevelAtom' t@, simply
-- using @traverse@ for @PlusLevel'@ would not be not correct.
instance Instantiate PlusLevel where
  instantiate' (Plus n a) = Plus n <$> instantiate' a

instance Instantiate LevelAtom where
  instantiate' l = case l of
    MetaLevel m vs -> do
      v <- instantiate' (MetaV m vs)
      case v of
        MetaV m vs -> return $ MetaLevel m vs
        _          -> return $ UnreducedLevel v
    UnreducedLevel l -> UnreducedLevel <$> instantiate' l
    _ -> return l

instance Instantiate a => Instantiate (Blocked a) where
  instantiate' v@NotBlocked{} = return v
  instantiate' v@(Blocked b u) = instantiate' b >>= \ case
    b | b == alwaysUnblock -> notBlocked <$> instantiate' u
      | otherwise          -> return $ Blocked b u

instance Instantiate Blocker where
  instantiate' (UnblockOnAll bs) = unblockOnAll . Set.fromList <$> mapM instantiate' (Set.toList bs)
  instantiate' (UnblockOnAny bs) = unblockOnAny . Set.fromList <$> mapM instantiate' (Set.toList bs)
  instantiate' b@(UnblockOnMeta x) =
    ifM (isInstantiatedMeta x) (return alwaysUnblock) (return b)

instance Instantiate Sort where
  instantiate' s = case s of
    MetaS x es -> instantiate' (MetaV x es) >>= \case
      Sort s'      -> return s'
      MetaV x' es' -> return $ MetaS x' es'
      Def d es'     -> return $ DefS d es'
      _            -> __IMPOSSIBLE__
    _ -> return s

instance (Instantiate t, Instantiate e) => Instantiate (Dom' t e) where
    instantiate' (Dom i fin n tac x) = Dom i fin n <$> instantiate' tac <*> instantiate' x

instance Instantiate a => Instantiate (Closure a) where
    instantiate' cl = do
        x <- enterClosure cl instantiate'
        return $ cl { clValue = x }

instance Instantiate a => Instantiate (Het s a) where

instance Instantiate ContextHet where
  instantiate' = go
    where
      go Empty = return Empty
      go (x@(n, v) :<| vs) = (:<|) <$> ((n,) <$> instantiate' v) <*> (go vs)

instance Instantiate Constraint where
  instantiate' (ValueCmp cmp t u v) = do
    (t,u,v) <- instantiate' (t,u,v)
    return $ ValueCmp cmp t u v
  instantiate' (ValueCmpHet cmp tel t u v) = do
    (tel,(t,u,v)) <- instantiate' (tel,(t,u,v))
    return $ ValueCmpHet cmp tel t u v
  instantiate' (ValueCmpOnFace cmp p t u v) = do
    ((p,t),u,v) <- instantiate' ((p,t),u,v)
    return $ ValueCmpOnFace cmp p t u v
  instantiate' (ElimCmp cmp fs t v as bs) =
    ElimCmp cmp fs <$> instantiate' t <*> instantiate' v <*> instantiate' as <*> instantiate' bs
  instantiate' (ElimCmpHet ctx cmp fs t as bs) =
    ElimCmpHet <$> instantiate' ctx <*> pure cmp <*> pure fs <*> instantiate' t <*> instantiate' as <*> instantiate' bs
  instantiate' (LevelCmp cmp u v)   = uncurry (LevelCmp cmp) <$> instantiate' (u,v)
  instantiate' (TelCmp a b cmp tela telb) = uncurry (TelCmp a b cmp)  <$> instantiate' (tela,telb)
  instantiate' (TelCmpHet ctx a b cmp tela telb) =
    TelCmpHet <$> instantiate' ctx <*> pure a <*> pure b <*> pure cmp <*> instantiate' tela <*> instantiate' telb
  instantiate' (SortCmp cmp a b)    = uncurry (SortCmp cmp) <$> instantiate' (a,b)
  instantiate' (Guarded c pid)      = Guarded <$> instantiate' c <*> pure pid
  instantiate' (UnBlock m)          = return $ UnBlock m
  instantiate' (FindInstance m b args) = FindInstance m b <$> mapM instantiate' args
  instantiate' (IsEmpty r t)        = IsEmpty r <$> instantiate' t
  instantiate' (CheckSizeLtSat t)   = CheckSizeLtSat <$> instantiate' t
  instantiate' c@CheckFunDef{}      = return c
  instantiate' (HasBiggerSort a)    = HasBiggerSort <$> instantiate' a
  instantiate' (HasPTSRule a b)     = uncurry HasPTSRule <$> instantiate' (a,b)
  instantiate' (UnquoteTactic t h g) = UnquoteTactic <$> instantiate' t <*> instantiate' h <*> instantiate' g
  instantiate' c@CheckMetaInst{}    = return c

instance Instantiate TwinT where

instance Instantiate a => Instantiate (CompareAs' a) where

instance Instantiate Candidate where
  instantiate' (Candidate q u t ov) = Candidate q <$> instantiate' u <*> instantiate' t <*> pure ov

instance Instantiate EqualityView where
  instantiate' (OtherType t)            = OtherType
    <$> instantiate' t
  instantiate' (EqualityType s eq l t a b) = EqualityType
    <$> instantiate' s
    <*> return eq
    <*> mapM instantiate' l
    <*> instantiate' t
    <*> instantiate' a
    <*> instantiate' b

---------------------------------------------------------------------------
-- * Reduction to weak head normal form.
---------------------------------------------------------------------------

-- | Is something (an elimination of) a meta variable?
--   Does not perform any reductions.

class IsMeta a where
  isMeta :: a -> Maybe MetaId

instance IsMeta Term where
  isMeta (MetaV m _) = Just m
  isMeta _           = Nothing

instance IsMeta a => IsMeta (Sort' a) where
  isMeta (MetaS m _) = Just m
  isMeta _           = Nothing

instance IsMeta a => IsMeta (Type'' t a) where
  isMeta = isMeta . unEl

instance IsMeta a => IsMeta (Elim' a) where
  isMeta Proj{}    = Nothing
  isMeta IApply{}  = Nothing
  isMeta (Apply a) = isMeta a

instance IsMeta a => IsMeta (Arg a) where
  isMeta = isMeta . unArg

instance IsMeta a => IsMeta (Level' a) where
  isMeta (Max 0 [l]) = isMeta l
  isMeta _           = Nothing

instance IsMeta a => IsMeta (PlusLevel' a) where
  isMeta (Plus 0 l)  = isMeta l
  isMeta _           = Nothing

instance IsMeta a => IsMeta (LevelAtom' a) where
  isMeta = \case
    MetaLevel m _    -> Just m
    BlockedLevel _ t -> isMeta t
    NeutralLevel _ t -> isMeta t
    UnreducedLevel t -> isMeta t

-- instance IsMeta TwinT where
--  isMeta (UnsafeSingleT a) = isMeta a

instance IsMeta CompareAs where
  isMeta (AsTermsOf a) = isMeta a
  isMeta AsSizes       = Nothing
  isMeta AsTypes       = Nothing

-- | Case on whether a term is blocked on a meta (or is a meta).
--   That means it can change its shape when the meta is instantiated.
ifBlocked
  :: (Reduce t, IsMeta t, MonadReduce m)
  => t -> (Blocker -> t -> m a) -> (NotBlocked -> t -> m a) -> m a
ifBlocked t blocked unblocked = do
  ifBlocked' t >>= \case
    Left  x -> uncurry blocked x
    Right x -> uncurry unblocked x

ifBlocked' :: (Reduce t, IsMeta t, MonadReduce m) =>
  t -> m (Either (Blocker, t) (NotBlocked, t))
ifBlocked' t  = do
  t <- reduceB t
  return$ case t of
    Blocked m t -> Left (m, t)
    NotBlocked nb t -> case isMeta t of
      Just m    -> Left (unblockOnMeta m, t)
      Nothing   -> Right (nb, t)

-- | Throw pattern violation if blocked or a meta.
abortIfBlocked :: (MonadReduce m, MonadTCError m, IsMeta t, Reduce t) => t -> m t
abortIfBlocked t = ifBlocked t (const . patternViolation) (const return)

isBlocked
  :: (Reduce t, IsMeta t, MonadReduce m)
  => t -> m (Maybe Blocker)
isBlocked t = ifBlocked t (\m _ -> return $ Just m) (\_ _ -> return Nothing)

class Reduce t where
    reduce'  :: t -> ReduceM t
    reduceB' :: t -> ReduceM (Blocked t)

    reduce'  t = ignoreBlocking <$> reduceB' t
    reduceB' t = notBlocked <$> reduce' t

instance Reduce Type where
    reduce'  (El s t) = workOnTypes $ El s <$> reduce' t
    reduceB' (El s t) = workOnTypes $ fmap (El s) <$> reduceB' t

instance Reduce Sort where
    reduce' s = do
      s <- instantiate' s
      case s of
        PiSort a s2 -> do
          (s1' , s2') <- reduce' (getSort a , s2)
          let a' = set lensSort s1' a
          maybe (return $ PiSort a' s2') reduce' $ piSort' a' s2'
        FunSort s1 s2 -> do
          (s1' , s2') <- reduce (s1 , s2)
          maybe (return $ FunSort s1' s2') reduce' $ funSort' s1' s2'
        UnivSort s' -> do
          s' <- reduce' s'
          caseMaybe (univSort' s') (return $ UnivSort s') reduce'
        Prop s'    -> Prop <$> reduce' s'
        Type s'    -> Type <$> reduce' s'
        Inf n      -> return $ Inf n
        SizeUniv   -> return SizeUniv
        MetaS x es -> return s
        DefS d es  -> return s -- postulated sorts do not reduce
        DummyS{}   -> return s

instance Reduce Elim where
  reduce' (Apply v) = Apply <$> reduce' v
  reduce' (Proj o f)= pure $ Proj o f
  reduce' (IApply x y v) = IApply <$> reduce' x <*> reduce' y <*> reduce' v

instance Reduce Level where
  reduce'  (Max m as) = levelMax m <$> mapM reduce' as
  reduceB' (Max m as) = fmap (levelMax m) . blockAny <$> traverse reduceB' as

instance Reduce PlusLevel where
  reduceB' (Plus n l) = fmap (Plus n) <$> reduceB' l

instance Reduce LevelAtom where
  reduceB' l = case l of
    MetaLevel m vs   -> fromTm (MetaV m vs)
    NeutralLevel r v -> return $ NotBlocked r $ NeutralLevel r v
    BlockedLevel b v -> instantiate' b >>= \ case
      b | b == alwaysUnblock -> fromTm v
        | otherwise          -> return $ Blocked b $ BlockedLevel b v
    UnreducedLevel v -> fromTm v
    where
      fromTm v = do
        bv <- reduceB' v
        hasAllReductions <- (allReductions `SmallSet.isSubsetOf`) <$>
                              asksTC envAllowedReductions
        let v = ignoreBlocking bv
        case bv of
          NotBlocked r (MetaV m vs) -> return $ NotBlocked r $ MetaLevel m vs
          Blocked m _               -> return $ Blocked m    $ BlockedLevel m v
          NotBlocked r _
            | hasAllReductions -> return $ NotBlocked r $ NeutralLevel r v
            | otherwise        -> return $ NotBlocked r $ UnreducedLevel v


instance (Subst t a, Reduce a) => Reduce (Abs a) where
  reduce' b@(Abs x _) = Abs x <$> underAbstraction_ b reduce'
  reduce' (NoAbs x v) = NoAbs x <$> reduce' v

-- Lists are never blocked
instance Reduce t => Reduce [t] where
    reduce' = traverse reduce'

instance Reduce t => Reduce (Arg t) where
    reduce' a = case getRelevance a of
      Irrelevant -> return a             -- Don't reduce' irr. args!?
                                         -- Andreas, 2018-03-03, caused #2989.
      _          -> traverse reduce' a

    reduceB' t = traverse id <$> traverse reduceB' t

instance Reduce t => Reduce (Dom t) where
    reduce' = traverse reduce'
    reduceB' t = traverse id <$> traverse reduceB' t

instance (Reduce a, Reduce b) => Reduce (a,b) where
    reduce' (x,y)  = (,) <$> reduce' x <*> reduce' y
    reduceB' (x,y) = do
      x <- reduceB' x
      y <- reduceB' y
      let blk = void x `mappend` void y
          xy  = (ignoreBlocking x , ignoreBlocking y)
      return $ blk $> xy

instance (Reduce a, Reduce b,Reduce c) => Reduce (a,b,c) where
    reduce' (x,y,z) = (,,) <$> reduce' x <*> reduce' y <*> reduce' z
    reduceB' (x,y,z) = do
      x <- reduceB' x
      y <- reduceB' y
      z <- reduceB' z
      let blk = void x `mappend` void y `mappend` void z
          xyz = (ignoreBlocking x , ignoreBlocking y , ignoreBlocking z)
      return $ blk $> xyz

reduceIApply :: ReduceM (Blocked Term) -> [Elim] -> ReduceM (Blocked Term)
reduceIApply = reduceIApply' reduceB'

blockedOrMeta :: Blocked Term -> Blocked ()
blockedOrMeta r =
  case r of
    Blocked b _              -> Blocked b ()
    NotBlocked _ (MetaV m _) -> blocked_ m
    NotBlocked i _           -> NotBlocked i ()

reduceIApply' :: (Term -> ReduceM (Blocked Term)) -> ReduceM (Blocked Term) -> [Elim] -> ReduceM (Blocked Term)
reduceIApply' red d (IApply x y r : es) = do
  view <- intervalView'
  r <- reduceB' r
  -- We need to propagate the blocking information so that e.g.
  -- we postpone "someNeutralPath ?0 = a" rather than fail.
  let blockedInfo = blockedOrMeta r

  case view (ignoreBlocking r) of
   IZero -> red (applyE x es)
   IOne  -> red (applyE y es)
   _     -> fmap (<* blockedInfo) (reduceIApply' red d es)
reduceIApply' red d (_ : es) = reduceIApply' red d es
reduceIApply' _   d [] = d

instance Reduce DeBruijnPattern where
  reduceB' (DotP o v) = fmap (DotP o) <$> reduceB' v
  reduceB' p          = return $ notBlocked p

instance Reduce Term where
  reduceB' = {-# SCC "reduce'<Term>" #-} maybeFastReduceTerm

shouldTryFastReduce :: ReduceM Bool
shouldTryFastReduce = (optFastReduce <$> pragmaOptions) `and2M` do
  allowed <- asksTC envAllowedReductions
  let optionalReductions = SmallSet.fromList [NonTerminatingReductions, UnconfirmedReductions]
      requiredReductions = allReductions SmallSet.\\ optionalReductions
  return $ (allowed SmallSet.\\ optionalReductions) == requiredReductions

maybeFastReduceTerm :: Term -> ReduceM (Blocked Term)
maybeFastReduceTerm v = do
  let tryFast = case v of
                  Def{}   -> True
                  Con{}   -> True
                  MetaV{} -> True
                  _       -> False
  if not tryFast then slowReduceTerm v
                 else
    case v of
      MetaV x _ -> ifM (isOpen x) (return $ notBlocked v) (maybeFast v)
      _         -> maybeFast v
  where
    isOpen x = isOpenMeta . mvInstantiation <$> lookupMeta x
    maybeFast v = ifM shouldTryFastReduce (fastReduce v) (slowReduceTerm v)

slowReduceTerm :: Term -> ReduceM (Blocked Term)
slowReduceTerm v = do
    v <- instantiate' v
    let done = return $ notBlocked v
        iapp = reduceIApply done
    case v of
--    Andreas, 2012-11-05 not reducing meta args does not destroy anything
--    and seems to save 2% sec on the standard library
--      MetaV x args -> notBlocked . MetaV x <$> reduce' args
      MetaV x es -> iapp es
      Def f es   -> flip reduceIApply es $ unfoldDefinitionE False reduceB' (Def f []) f es
      Con c ci es -> do
          -- Constructors can reduce' when they come from an
          -- instantiated module.
          -- also reduce when they are path constructors
          v <- flip reduceIApply es
                 $ unfoldDefinitionE False reduceB' (Con c ci []) (conName c) es
          traverse reduceNat v
      Sort s   -> fmap Sort <$> reduceB' s
      Level l  -> ifM (SmallSet.member LevelReductions <$> asksTC envAllowedReductions)
                    {- then -} (fmap levelTm <$> reduceB' l)
                    {- else -} done
      Pi _ _   -> done
      Lit _    -> done
      Var _ es  -> iapp es
      Lam _ _  -> done
      DontCare _ -> done
      Dummy{}    -> done
    where
      -- NOTE: reduceNat can traverse the entire term.
      reduceNat v@(Con c ci []) = do
        mz  <- getBuiltin' builtinZero
        case v of
          _ | Just v == mz  -> return $ Lit $ LitNat 0
          _                 -> return v
      reduceNat v@(Con c ci [Apply a]) | visible a && isRelevant a = do
        ms  <- getBuiltin' builtinSuc
        case v of
          _ | Just (Con c ci []) == ms -> inc <$> reduce' (unArg a)
          _                         -> return v
          where
            inc = \case
              Lit (LitNat n) -> Lit $ LitNat $ n + 1
              w              -> Con c ci [Apply $ defaultArg w]
      reduceNat v = return v

-- Andreas, 2013-03-20 recursive invokations of unfoldCorecursion
-- need also to instantiate metas, see Issue 826.
unfoldCorecursionE :: Elim -> ReduceM (Blocked Elim)
unfoldCorecursionE (Proj o p)           = notBlocked . Proj o <$> getOriginalProjection p
unfoldCorecursionE (Apply (Arg info v)) = fmap (Apply . Arg info) <$>
  unfoldCorecursion v
unfoldCorecursionE (IApply x y r) = do -- TODO check if this makes sense
   [x,y,r] <- mapM unfoldCorecursion [x,y,r]
   return $ IApply <$> x <*> y <*> r

unfoldCorecursion :: Term -> ReduceM (Blocked Term)
unfoldCorecursion v = do
  v <- instantiate' v
  case v of
    Def f es -> unfoldDefinitionE True unfoldCorecursion (Def f []) f es
    _ -> slowReduceTerm v

-- | If the first argument is 'True', then a single delayed clause may
-- be unfolded.
unfoldDefinition ::
  Bool -> (Term -> ReduceM (Blocked Term)) ->
  Term -> QName -> Args -> ReduceM (Blocked Term)
unfoldDefinition unfoldDelayed keepGoing v f args =
  unfoldDefinitionE unfoldDelayed keepGoing v f (map Apply args)

unfoldDefinitionE ::
  Bool -> (Term -> ReduceM (Blocked Term)) ->
  Term -> QName -> Elims -> ReduceM (Blocked Term)
unfoldDefinitionE unfoldDelayed keepGoing v f es = do
  r <- unfoldDefinitionStep unfoldDelayed v f es
  case r of
    NoReduction v    -> return v
    YesReduction _ v -> keepGoing v

unfoldDefinition' ::
  Bool -> (Simplification -> Term -> ReduceM (Simplification, Blocked Term)) ->
  Term -> QName -> Elims -> ReduceM (Simplification, Blocked Term)
unfoldDefinition' unfoldDelayed keepGoing v0 f es = do
  r <- unfoldDefinitionStep unfoldDelayed v0 f es
  case r of
    NoReduction v       -> return (NoSimplification, v)
    YesReduction simp v -> keepGoing simp v

unfoldDefinitionStep :: Bool -> Term -> QName -> Elims -> ReduceM (Reduced (Blocked Term) Term)
unfoldDefinitionStep unfoldDelayed v0 f es =
  {-# SCC "reduceDef" #-} do
  traceSDoc "tc.reduce" 90 ("unfoldDefinitionStep v0" <+> prettyTCM v0) $ do
  info <- getConstInfo f
  rewr <- instantiateRewriteRules =<< getRewriteRulesFor f
  allowed <- asksTC envAllowedReductions
  prp <- isPropM $ defType info
  let def = theDef info
      v   = v0 `applyE` es
      -- Non-terminating functions
      -- (i.e., those that failed the termination check)
      -- and delayed definitions
      -- are not unfolded unless explicitly permitted.
      dontUnfold =
        (defNonterminating info && SmallSet.notMember NonTerminatingReductions allowed)
        || (defTerminationUnconfirmed info && SmallSet.notMember UnconfirmedReductions allowed)
        || (defDelayed info == Delayed && not unfoldDelayed)
        || prp || isIrrelevant (defArgInfo info)
      copatterns = defCopatternLHS info
  case def of
    Constructor{conSrcCon = c} ->
      noReduction $ notBlocked $ Con (c `withRangeOf` f) ConOSystem [] `applyE` es
    Primitive{primAbstr = ConcreteDef, primName = x, primClauses = cls} -> do
      pf <- fromMaybe __IMPOSSIBLE__ <$> getPrimitive' x
      if FunctionReductions `SmallSet.member` allowed
        then reducePrimitive x v0 f es pf dontUnfold
                             cls (defCompiled info) rewr
        else noReduction $ notBlocked v
    PrimitiveSort{ primSort = s } -> yesReduction NoSimplification $ Sort s `applyE` es
    _  -> do
      if (RecursiveReductions `SmallSet.member` allowed) ||
         (isJust (isProjection_ def) && ProjectionReductions `SmallSet.member` allowed) || -- includes projection-like
         (isInlineFun def && InlineReductions `SmallSet.member` allowed) ||
         (definitelyNonRecursive_ def && copatterns && CopatternReductions `SmallSet.member` allowed) ||
         (definitelyNonRecursive_ def && FunctionReductions `SmallSet.member` allowed)
        then
          reduceNormalE v0 f (map notReduced es) dontUnfold
                       (defClauses info) (defCompiled info) rewr
        else noReduction $ notBlocked v  -- Andrea(s), 2014-12-05 OK?

  where
    noReduction    = return . NoReduction
    yesReduction s = return . YesReduction s
    reducePrimitive x v0 f es pf dontUnfold cls mcc rewr
      | length es < ar
                  = noReduction $ NotBlocked Underapplied $ v0 `applyE` es -- not fully applied
      | otherwise = {-# SCC "reducePrimitive" #-} do
          let (es1,es2) = splitAt ar es
              args1     = fromMaybe __IMPOSSIBLE__ $ mapM isApplyElim es1
          r <- primFunImplementation pf args1 (length es2)
          case r of
            NoReduction args1' -> do
              let es1' = map (fmap Apply) args1'
              if null cls && null rewr then do
                noReduction $ applyE (Def f []) <$> do
                  blockAll $ map mredToBlocked es1' ++ map notBlocked es2
               else
                reduceNormalE v0 f (es1' ++ map notReduced es2) dontUnfold cls mcc rewr
            YesReduction simpl v -> yesReduction simpl $ v `applyE` es2
      where
          ar  = primFunArity pf

          mredToBlocked :: IsMeta t => MaybeReduced t -> Blocked t
          mredToBlocked (MaybeRed NotReduced  e) = notBlocked e
          mredToBlocked (MaybeRed (Reduced NotBlocked{}) e) | Just x <- isMeta e = e <$ blocked_ x -- reduced metas should be blocked
          mredToBlocked (MaybeRed (Reduced b) e) = e <$ b

    reduceNormalE :: Term -> QName -> [MaybeReduced Elim] -> Bool -> [Clause] -> Maybe CompiledClauses -> RewriteRules -> ReduceM (Reduced (Blocked Term) Term)
    reduceNormalE v0 f es dontUnfold def mcc rewr = {-# SCC "reduceNormal" #-} do
      traceSDoc "tc.reduce" 90 ("reduceNormalE v0 =" <+> prettyTCM v0) $ do
      case (def,rewr) of
        _ | dontUnfold -> traceSLn "tc.reduce" 90 "reduceNormalE: don't unfold (non-terminating or delayed)" $
                          defaultResult -- non-terminating or delayed
        ([],[])        -> traceSLn "tc.reduce" 90 "reduceNormalE: no clauses or rewrite rules" $ do
          -- no definition for head
          blk <- defBlocked <$> getConstInfo f
          noReduction $ blk $> vfull
        (cls,rewr)     -> do
          ev <- appDefE_ f v0 cls mcc rewr es
          debugReduce ev
          return ev
      where
      defaultResult = noReduction $ NotBlocked ReallyNotBlocked vfull
      vfull         = v0 `applyE` map ignoreReduced es
      debugReduce ev = verboseS "tc.reduce" 90 $ do
        case ev of
          NoReduction v -> do
            reportSDoc "tc.reduce" 90 $ vcat
              [ "*** tried to reduce " <+> prettyTCM f
              , "    es =  " <+> sep (map (prettyTCM . ignoreReduced) es)
              -- , "*** tried to reduce " <+> prettyTCM vfull
              , "    stuck on" <+> prettyTCM (ignoreBlocking v)
              ]
          YesReduction _simpl v -> do
            reportSDoc "tc.reduce"  90 $ "*** reduced definition: " <+> prettyTCM f
            reportSDoc "tc.reduce"  95 $ "    result" <+> prettyTCM v
            reportSDoc "tc.reduce" 100 $ "    raw   " <+> text (show v)

-- | Reduce a non-primitive definition if it is a copy linking to another def.
reduceDefCopy :: forall m. (MonadReduce m, HasConstInfo m, HasOptions m,
                            ReadTCState m, MonadTCEnv m, MonadDebug m)
              => QName -> Elims -> m (Reduced () Term)
reduceDefCopy f es = do
  info <- getConstInfo f
  rewr <- instantiateRewriteRules =<< getRewriteRulesFor f
  if (defCopy info) then reduceDef_ info rewr f es else return $ NoReduction ()
  where
    reduceDef_ :: Definition -> RewriteRules -> QName -> Elims -> m (Reduced () Term)
    reduceDef_ info rewr f es = do
      let v0   = Def f []
          cls  = (defClauses info)
          mcc  = (defCompiled info)
      if (defDelayed info == Delayed) || (defNonterminating info)
       then return $ NoReduction ()
       else do
          ev <- liftReduce $ appDefE_ f v0 cls mcc rewr $ map notReduced es
          case ev of
            YesReduction simpl t -> return $ YesReduction simpl t
            NoReduction{}        -> return $ NoReduction ()

-- | Reduce simple (single clause) definitions.
reduceHead :: (HasBuiltins m, HasConstInfo m, MonadReduce m, MonadDebug m)
           => Term -> m (Blocked Term)
reduceHead v = do -- ignoreAbstractMode $ do
  -- Andreas, 2013-02-18 ignoreAbstractMode leads to information leakage
  -- see Issue 796

  -- first, possibly rewrite literal v to constructor form
  v <- constructorForm v
  traceSDoc "tc.inj.reduce" 30 (ignoreAbstractMode $ "reduceHead" <+> prettyTCM v) $ do
  case v of
    Def f es -> do

      abstractMode <- envAbstractMode <$> askTC
      isAbstract <- treatAbstractly f
      traceSLn "tc.inj.reduce" 50 (
        "reduceHead: we are in " ++ show abstractMode++ "; " ++ prettyShow f ++
        " is treated " ++ if isAbstract then "abstractly" else "concretely"
        ) $ do
      let v0  = Def f []
          red = liftReduce $ unfoldDefinitionE False reduceHead v0 f es
      def <- theDef <$> getConstInfo f
      case def of
        -- Andreas, 2012-11-06 unfold aliases (single clause terminating functions)
        -- see test/succeed/Issue747
        -- We restrict this to terminating functions to not make the
        -- type checker loop here on non-terminating functions.
        -- see test/fail/TerminationInfiniteRecord
        Function{ funClauses = [ _ ], funDelayed = NotDelayed, funTerminates = Just True } -> do
          traceSLn "tc.inj.reduce" 50 ("reduceHead: head " ++ prettyShow f ++ " is Function") $ do
          red
        Datatype{ dataClause = Just _ } -> red
        Record{ recClause = Just _ }    -> red
        _                               -> return $ notBlocked v
    _ -> return $ notBlocked v

-- | Unfold a single inlined function.
unfoldInlined :: (HasConstInfo m, MonadReduce m) => Term -> m Term
unfoldInlined v = do
  inTypes <- viewTC eWorkingOnTypes
  case v of
    _ | inTypes -> return v -- Don't inline in types (to avoid unfolding of goals)
    Def f es -> do
      info <- getConstInfo f
      let def = theDef info
          irr = isIrrelevant $ defArgInfo info
      case def of   -- Only for simple definitions with no pattern matching (TODO: maybe copatterns?)
        Function{ funCompiled = Just Done{}, funDelayed = NotDelayed }
          | def ^. funInline , not irr -> liftReduce $
          ignoreBlocking <$> unfoldDefinitionE False (return . notBlocked) (Def f []) f es
        _ -> return v
    _ -> return v

-- | Apply a definition using the compiled clauses, or fall back to
--   ordinary clauses if no compiled clauses exist.
appDef_ :: QName -> Term -> [Clause] -> Maybe CompiledClauses -> RewriteRules -> MaybeReducedArgs -> ReduceM (Reduced (Blocked Term) Term)
appDef_ f v0 cls mcc rewr args = appDefE_ f v0 cls mcc rewr $ map (fmap Apply) args

appDefE_ :: QName -> Term -> [Clause] -> Maybe CompiledClauses -> RewriteRules -> MaybeReducedElims -> ReduceM (Reduced (Blocked Term) Term)
appDefE_ f v0 cls mcc rewr args =
  localTC (\ e -> e { envAppDef = Just f }) $
  maybe (appDefE' v0 cls rewr args)
        (\cc -> appDefE v0 cc rewr args) mcc


-- | Apply a defined function to it's arguments, using the compiled clauses.
--   The original term is the first argument applied to the third.
appDef :: Term -> CompiledClauses -> RewriteRules -> MaybeReducedArgs -> ReduceM (Reduced (Blocked Term) Term)
appDef v cc rewr args = appDefE v cc rewr $ map (fmap Apply) args

appDefE :: Term -> CompiledClauses -> RewriteRules -> MaybeReducedElims -> ReduceM (Reduced (Blocked Term) Term)
appDefE v cc rewr es = do
  traceSDoc "tc.reduce" 90 ("appDefE v = " <+> prettyTCM v) $ do
  r <- matchCompiledE cc es
  case r of
    YesReduction simpl t -> return $ YesReduction simpl t
    NoReduction es'      -> rewrite (void es') (applyE v) rewr (ignoreBlocking es')

-- | Apply a defined function to it's arguments, using the original clauses.
appDef' :: Term -> [Clause] -> RewriteRules -> MaybeReducedArgs -> ReduceM (Reduced (Blocked Term) Term)
appDef' v cls rewr args = appDefE' v cls rewr $ map (fmap Apply) args

appDefE' :: Term -> [Clause] -> RewriteRules -> MaybeReducedElims -> ReduceM (Reduced (Blocked Term) Term)
appDefE' v cls rewr es = traceSDoc "tc.reduce" 90 ("appDefE' v = " <+> prettyTCM v) $ do
  goCls cls $ map ignoreReduced es
  where
    goCls :: [Clause] -> [Elim] -> ReduceM (Reduced (Blocked Term) Term)
    goCls cl es = do
      case cl of
        -- Andreas, 2013-10-26  In case of an incomplete match,
        -- we just do not reduce.  This allows adding single function
        -- clauses after they have been type-checked, to type-check
        -- the remaining clauses (see Issue 907).
        -- Andrea(s), 2014-12-05:  We return 'MissingClauses' here, since this
        -- is the most conservative reason.
        [] -> rewrite (NotBlocked MissingClauses ()) (applyE v) rewr es
        cl : cls -> do
          let pats = namedClausePats cl
              body = clauseBody cl
              npats = length pats
              nvars = size $ clauseTel cl
          -- if clause is underapplied, skip to next clause
          if length es < npats then goCls cls es else do
            let (es0, es1) = splitAt npats es
            (m, es0) <- matchCopatterns pats es0
            let es = es0 ++ es1
            case m of
              No         -> goCls cls es
              DontKnow b -> rewrite b (applyE v) rewr es
              Yes simpl vs -- vs is the subst. for the variables bound in body
                | Just w <- body -> do -- clause has body?
                    -- TODO: let matchPatterns also return the reduced forms
                    -- of the original arguments!
                    -- Andreas, 2013-05-19 isn't this done now?
                    let sigma = buildSubstitution __IMPOSSIBLE__ nvars vs
                    return $ YesReduction simpl $ applySubst sigma w `applyE` es1
                | otherwise     -> rewrite (NotBlocked AbsurdMatch ()) (applyE v) rewr es

instance Reduce a => Reduce (Closure a) where
    reduce' cl = do
        x <- enterClosure cl reduce'
        return $ cl { clValue = x }

instance (Subst t a, Reduce a) => Reduce (Tele a) where
  reduce' EmptyTel          = return EmptyTel
  reduce' (ExtendTel a tel) = ExtendTel <$> reduce' a <*> reduce' tel

class ReduceHet a where
  reduceHet' :: ContextHet -> a -> ReduceM a
  default reduceHet' :: (Traversable t, a ~ t b, ReduceHet b) => ContextHet -> a -> ReduceM a
  reduceHet' = traverse . reduceHet'

instance ReduceHet TwinT where
  reduceHet' :: ContextHet -> TwinT -> ReduceM TwinT
  reduceHet' tel (SingleT a) = SingleT <$> underHet @'Both tel reduce' a
  reduceHet' tel t@(TwinT{necessary,twinPid,twinLHS,twinRHS,twinCompat}) = do
    twinLHS <- underHet @'LHS tel reduce' twinLHS
    twinRHS <- underHet @'RHS tel reduce' twinRHS
    twinCompat <- underHet @'Compat tel reduce' twinCompat
    return TwinT{necessary,twinPid,twinLHS,twinRHS,twinCompat}

instance {-# OVERLAPPING #-} ReduceHet a => ReduceHet (Het 'Whole a)

-- 2020-07-07 TODO Make more efficient, or give up on names altogether
-- instance ReduceHet ContextHet where
--   reduceHet' env = go (telToList env)
--     where
--       go :: [Dom (ArgName, TwinT)] -> ContextHet -> ReduceM ContextHet
--       go env EmptyTel = return EmptyTel
--       go env (ExtendTel a (Abs x tel)) = ExtendTel <$> reduceHet' (telFromList env) a <*> (Abs x <$> go (env ++ [fmap (x,) a]) tel)
--       go env (ExtendTel a (NoAbs{}))   = __IMPOSSIBLE__

instance ReduceHet a => ReduceHet (Dom a)
instance ReduceHet a => ReduceHet (CompareAs' a)

instance Reduce ContextHet where
  reduce' = go Empty
    where
      go env Empty = return Empty
      go env (x@(n, v) :<| vs) = (:<|) <$> ((n,) <$> reduceHet' env v) <*> (go (env :|> x) vs)

instance (Sing s, HetSideIsType s ~ 'True, Reduce a) => ReduceHet (Het s a) where
  reduceHet' tel a = underHet @s tel reduce' a

instance Reduce Constraint where
  reduce' (ValueCmp cmp t u v) = do
    (t,u,v) <- reduce' (t,u,v)
    return $ ValueCmp cmp t u v
  reduce' (ValueCmpHet cmp tel t u v) = do
    -- 2020-07-07 TODO <victor> Should one actually reduce the heterogeneous context?
    tel <- reduce' tel
    t' <- reduceHet' tel t
    u' <- reduceHet' tel u
    v' <- reduceHet' tel v
    return $ ValueCmpHet cmp tel t' u' v'
  reduce' (ValueCmpOnFace cmp p t u v) = do
    ((p,t),u,v) <- reduce' ((p,t),u,v)
    return $ ValueCmpOnFace cmp p t u v
  reduce' (ElimCmp cmp fs t v as bs) =
    ElimCmp cmp fs <$> reduce' t <*> reduce' v <*> reduce' as <*> reduce' bs
  reduce' (ElimCmpHet ctx cmp fs t as bs) =
    ElimCmpHet <$> reduce' ctx <*> pure cmp <*> pure fs <*> reduceHet' ctx t <*>  reduceHet' ctx as <*> reduceHet' ctx bs
  reduce' (LevelCmp cmp u v)    = uncurry (LevelCmp cmp) <$> reduce' (u,v)
  reduce' (TelCmp a b cmp tela telb) = uncurry (TelCmp a b cmp)  <$> reduce' (tela,telb)
  reduce' (TelCmpHet ctx a b cmp tela telb) =
    TelCmpHet <$> reduce' ctx <*> pure a <*> pure b <*> pure cmp <*> reduceHet' ctx tela <*> reduceHet' ctx telb
  reduce' (SortCmp cmp a b)     = uncurry (SortCmp cmp) <$> reduce' (a,b)
  reduce' (Guarded c pid)       = Guarded <$> reduce' c <*> pure pid
  reduce' (UnBlock m)           = return $ UnBlock m
  reduce' (FindInstance m b cands) = FindInstance m b <$> mapM reduce' cands
  reduce' (IsEmpty r t)         = IsEmpty r <$> reduce' t
  reduce' (CheckSizeLtSat t)    = CheckSizeLtSat <$> reduce' t
  reduce' c@CheckFunDef{}       = return c
  reduce' (HasBiggerSort a)     = HasBiggerSort <$> reduce' a
  reduce' (HasPTSRule a b)      = uncurry HasPTSRule <$> reduce' (a,b)
  reduce' (UnquoteTactic t h g) = UnquoteTactic <$> reduce' t <*> reduce' h <*> reduce' g
  reduce' c@CheckMetaInst{}     = return c

instance Reduce TwinT where
  reduce' = traverse reduce'

instance Reduce a => Reduce (CompareAs' a) where
  reduce' (AsTermsOf a) = AsTermsOf <$> reduce' a
  reduce' AsSizes       = return AsSizes
  reduce' AsTypes       = return AsTypes

instance Reduce e => Reduce (Map k e) where
    reduce' = traverse reduce'

instance Reduce Candidate where
  reduce' (Candidate q u t ov) = Candidate q <$> reduce' u <*> reduce' t <*> pure ov

instance Reduce EqualityView where
  reduce' (OtherType t)            = OtherType
    <$> reduce' t
  reduce' (EqualityType s eq l t a b) = EqualityType
    <$> reduce' s
    <*> return eq
    <*> mapM reduce' l
    <*> reduce' t
    <*> reduce' a
    <*> reduce' b

instance Reduce t => Reduce (IPBoundary' t) where
  reduce' = traverse reduce'
  reduceB' = fmap sequenceA . traverse reduceB'

---------------------------------------------------------------------------
-- * Simplification
---------------------------------------------------------------------------

-- | Only unfold definitions if this leads to simplification
--   which means that a constructor/literal pattern is matched.
class Simplify t where
  simplify' :: t -> ReduceM t

  default simplify' :: (t ~ f a, Traversable f, Simplify a) => t -> ReduceM t
  simplify' = traverse simplify'

-- boring instances:

instance Simplify t => Simplify [t]
instance Simplify t => Simplify (Map k t)
instance Simplify t => Simplify (Maybe t)
instance Simplify t => Simplify (Strict.Maybe t)

instance Simplify t => Simplify (Arg t)
instance Simplify t => Simplify (Elim' t)
instance Simplify t => Simplify (Named name t)
instance Simplify t => Simplify (IPBoundary' t)

instance (Simplify a, Simplify b) => Simplify (a,b) where
    simplify' (x,y) = (,) <$> simplify' x <*> simplify' y

instance (Simplify a, Simplify b, Simplify c) => Simplify (a,b,c) where
    simplify' (x,y,z) =
        do  (x,(y,z)) <- simplify' (x,(y,z))
            return (x,y,z)

instance Simplify Bool where
  simplify' = return

-- interesting instances:

instance Simplify Term where
  simplify' v = do
    v <- instantiate' v
    case v of
      Def f vs   -> do
        let keepGoing simp v = return (simp, notBlocked v)
        (simpl, v) <- unfoldDefinition' False keepGoing (Def f []) f vs
        traceSDoc "tc.simplify'" 90 (
          text ("simplify': unfolding definition returns " ++ show simpl)
            <+> prettyTCM (ignoreBlocking v)) $ do
        case simpl of
          YesSimplification -> simplifyBlocked' v -- Dangerous, but if @simpl@ then @v /= Def f vs@
          NoSimplification  -> Def f <$> simplify' vs
      MetaV x vs -> MetaV x  <$> simplify' vs
      Con c ci vs-> Con c ci <$> simplify' vs
      Sort s     -> Sort     <$> simplify' s
      Level l    -> levelTm  <$> simplify' l
      Pi a b     -> Pi       <$> simplify' a <*> simplify' b
      Lit l      -> return v
      Var i vs   -> Var i    <$> simplify' vs
      Lam h v    -> Lam h    <$> simplify' v
      DontCare v -> dontCare <$> simplify' v
      Dummy{}    -> return v

simplifyBlocked' :: Simplify t => Blocked t -> ReduceM t
simplifyBlocked' (Blocked _ t) = return t
simplifyBlocked' (NotBlocked _ t) = simplify' t  -- Andrea(s), 2014-12-05 OK?

instance Simplify t => Simplify (Type' t) where
    simplify' (El s t) = El <$> simplify' s <*> simplify' t

instance Simplify Sort where
    simplify' s = do
      case s of
        PiSort a s -> piSort <$> simplify' a <*> simplify' s
        FunSort s1 s2 -> funSort <$> simplify' s1 <*> simplify' s2
        UnivSort s -> univSort <$> simplify' s
        Type s     -> Type <$> simplify' s
        Prop s     -> Prop <$> simplify' s
        Inf _      -> return s
        SizeUniv   -> return s
        MetaS x es -> MetaS x <$> simplify' es
        DefS d es  -> DefS d <$> simplify' es
        DummyS{}   -> return s

instance Simplify Level where
  simplify' (Max m as) = levelMax m <$> simplify' as

instance Simplify PlusLevel where
  simplify' (Plus n l) = Plus n <$> simplify' l

instance Simplify LevelAtom where
  simplify' l = do
    l <- instantiate' l
    case l of
      MetaLevel m vs   -> MetaLevel m <$> simplify' vs
      BlockedLevel m v -> BlockedLevel m <$> simplify' v
      NeutralLevel r v -> NeutralLevel r <$> simplify' v -- ??
      UnreducedLevel v -> UnreducedLevel <$> simplify' v -- ??

instance (Subst t a, Simplify a) => Simplify (Abs a) where
    simplify' a@(Abs x _) = Abs x <$> underAbstraction_ a simplify'
    simplify' (NoAbs x v) = NoAbs x <$> simplify' v

instance Simplify t => Simplify (Dom t) where
    simplify' = traverse simplify'

instance Simplify a => Simplify (Closure a) where
    simplify' cl = do
        x <- enterClosure cl simplify'
        return $ cl { clValue = x }

instance (Subst t a, Simplify a) => Simplify (Tele a) where
  simplify' EmptyTel        = return EmptyTel
  simplify' (ExtendTel a b) = uncurry ExtendTel <$> simplify' (a, b)

instance Simplify ProblemConstraint where
  simplify' (PConstr pid unblock c) = PConstr pid unblock <$> simplify' c

class SimplifyInHet a where
  simplifyHet' :: ContextHet -> a -> ReduceM a
  default simplifyHet' :: (Traversable t, a ~ t b, SimplifyInHet b) => ContextHet -> a -> ReduceM a
  simplifyHet' = traverse . simplifyHet'

instance SimplifyInHet TwinT where
  simplifyHet' :: ContextHet -> TwinT -> ReduceM TwinT
  simplifyHet' tel (SingleT a) = SingleT <$> underHet @'Both tel simplify' a
  simplifyHet' tel t@(TwinT{necessary,twinPid,twinLHS,twinRHS,twinCompat}) = do
    twinLHS <- underHet @'LHS tel simplify' twinLHS
    twinRHS <- underHet @'RHS tel simplify' twinRHS
    twinCompat <- underHet @'Compat tel simplify' twinCompat
    return TwinT{necessary,twinPid,twinLHS,twinRHS,twinCompat}

-- 2020-07-07 TODO Make more efficient, or give up on names altogether
-- instance {-# OVERLAPPING #-} SimplifyInHet ContextHet where
--   simplifyHet' env = go (telToList env)
--     where
--       go :: [Dom (ArgName, TwinT)] -> ContextHet -> ReduceM ContextHet
--       go env EmptyTel = return EmptyTel
--       go env (ExtendTel a (Abs x tel)) = ExtendTel <$> simplifyHet' (telFromList env) a <*> (Abs x <$> go (env ++ [fmap (x,) a]) tel)
--       go env (ExtendTel a (NoAbs{}))   = __IMPOSSIBLE__

instance SimplifyInHet a => SimplifyInHet (Dom a)
instance SimplifyInHet a => SimplifyInHet (CompareAs' a)

instance (Sing s, HetSideIsType s ~ 'True, Simplify a) => SimplifyInHet (Het s a) where
  simplifyHet' tel a = underHet @s tel simplify' a

-- This is not actually overlapping, as HetSideIsType 'Whole ~ 'False, but GHC can't tell
instance {-# OVERLAPPING #-} SimplifyInHet a => SimplifyInHet (Het 'Whole a)

instance Simplify ContextHet where
  simplify' = go Empty
    where
      go env Empty = return Empty
      go env (x@(n, v) :<| vs) = (:<|) <$> ((n,) <$> simplifyHet' env v) <*> (go (env :|> x) vs)

instance Simplify Constraint where
  simplify' (ValueCmp cmp t u v) = do
    (t,u,v) <- simplify' (t,u,v)
    return $ ValueCmp cmp t u v
  simplify' (ValueCmpHet cmp tel t u v) = do
    -- 2020-07-07 TODO <victor> Should one actually simplify the heterogeneous context?
    tel <- simplify' tel
    t' <- traverse (simplifyHet' tel) t
    u' <- simplifyHet' tel u
    v' <- simplifyHet' tel v
    return $ ValueCmpHet cmp tel t' u' v'
  simplify' (ValueCmpOnFace cmp p t u v) = do
    ((p,t),u,v) <- simplify' ((p,t),u,v)
    return $ ValueCmp cmp (AsTermsOf t) u v
  simplify' (ElimCmp cmp fs t v as bs) =
    ElimCmp cmp fs <$> simplify' t <*> simplify' v <*> simplify' as <*> simplify' bs
  simplify' (ElimCmpHet ctx cmp fs t as bs) =
    ElimCmpHet <$> simplify' ctx <*> pure cmp <*> pure fs <*> simplifyHet' ctx t <*> simplifyHet' ctx as <*> simplifyHet' ctx bs
  simplify' (LevelCmp cmp u v)    = uncurry (LevelCmp cmp) <$> simplify' (u,v)
  simplify' (TelCmp a b cmp tela telb) = uncurry (TelCmp a b cmp) <$> simplify' (tela,telb)
  simplify' (TelCmpHet ctx a b cmp tela telb) =
    TelCmpHet <$> simplify' ctx <*> pure a <*> pure b <*> pure cmp <*> simplifyHet' ctx tela <*> simplifyHet' ctx telb
  simplify' (SortCmp cmp a b)     = uncurry (SortCmp cmp) <$> simplify' (a,b)
  simplify' (Guarded c pid)       = Guarded <$> simplify' c <*> pure pid
  simplify' (UnBlock m)           = return $ UnBlock m
  simplify' (FindInstance m b cands) = FindInstance m b <$> mapM simplify' cands
  simplify' (IsEmpty r t)         = IsEmpty r <$> simplify' t
  simplify' (CheckSizeLtSat t)    = CheckSizeLtSat <$> simplify' t
  simplify' c@CheckFunDef{}       = return c
  simplify' (HasBiggerSort a)     = HasBiggerSort <$> simplify' a
  simplify' (HasPTSRule a b)      = uncurry HasPTSRule <$> simplify' (a,b)
  simplify' (UnquoteTactic t h g) = UnquoteTactic <$> simplify' t <*> simplify' h <*> simplify' g
  simplify' c@CheckMetaInst{}     = return c

instance Simplify TwinT where
  simplify' = traverse simplify'

instance Simplify a => Simplify (CompareAs' a) where
  simplify' = traverse simplify'

-- UNUSED
-- instance Simplify ConPatternInfo where
--   simplify' (ConPatternInfo mr mt) = ConPatternInfo mr <$> simplify' mt

-- UNUSED
-- instance Simplify Pattern where
--   simplify' p = case p of
--     VarP _       -> return p
--     LitP _       -> return p
--     ConP c ci ps -> ConP c <$> simplify' ci <*> simplify' ps
--     DotP v       -> DotP <$> simplify' v
--     ProjP _      -> return p

instance Simplify DisplayForm where
  simplify' (Display n ps v) = Display n <$> simplify' ps <*> return v

instance Simplify Candidate where
  simplify' (Candidate q u t ov) = Candidate q <$> simplify' u <*> simplify' t <*> pure ov

instance Simplify EqualityView where
  simplify' (OtherType t)            = OtherType
    <$> simplify' t
  simplify' (EqualityType s eq l t a b) = EqualityType
    <$> simplify' s
    <*> return eq
    <*> mapM simplify' l
    <*> simplify' t
    <*> simplify' a
    <*> simplify' b

---------------------------------------------------------------------------
-- * Normalisation
---------------------------------------------------------------------------

class Normalise t where
  normalise' :: t -> ReduceM t

  default normalise' :: (t ~ f a, Traversable f, Normalise a) => t -> ReduceM t
  normalise' = traverse normalise'

-- boring instances:

instance Normalise t => Normalise [t]
instance Normalise t => Normalise (Map k t)
instance Normalise t => Normalise (Maybe t)
instance Normalise t => Normalise (Strict.Maybe t)

-- Arg not included since we do not normalize irrelevant subterms
-- Elim' not included since it contains Arg
instance Normalise t => Normalise (Named name t)
instance Normalise t => Normalise (IPBoundary' t)
instance Normalise t => Normalise (WithHiding t)

instance (Normalise a, Normalise b) => Normalise (a,b) where
    normalise' (x,y) = (,) <$> normalise' x <*> normalise' y

instance (Normalise a, Normalise b, Normalise c) => Normalise (a,b,c) where
    normalise' (x,y,z) =
        do  (x,(y,z)) <- normalise' (x,(y,z))
            return (x,y,z)

instance Normalise Bool where
  normalise' = return

instance Normalise Char where
  normalise' = return

instance Normalise Int where
  normalise' = return

instance Normalise DBPatVar where
  normalise' = return

-- interesting instances:

instance Normalise Sort where
    normalise' s = do
      s <- reduce' s
      case s of
        PiSort a s -> piSort <$> normalise' a <*> normalise' s
        FunSort s1 s2 -> funSort <$> normalise' s1 <*> normalise' s2
        UnivSort s -> univSort <$> normalise' s
        Prop s     -> Prop <$> normalise' s
        Type s     -> Type <$> normalise' s
        Inf _      -> return s
        SizeUniv   -> return SizeUniv
        MetaS x es -> return s
        DefS d es  -> return s
        DummyS{}   -> return s

instance Normalise t => Normalise (Type' t) where
    normalise' (El s t) = El <$> normalise' s <*> normalise' t

instance Normalise Term where
    normalise' v = ifM shouldTryFastReduce (fastNormalise v) (slowNormaliseArgs =<< reduce' v)

slowNormaliseArgs :: Term -> ReduceM Term
slowNormaliseArgs v = case v of
  Var n vs    -> Var n      <$> normalise' vs
  Con c ci vs -> Con c ci   <$> normalise' vs
  Def f vs    -> Def f      <$> normalise' vs
  MetaV x vs  -> MetaV x    <$> normalise' vs
  Lit _       -> return v
  Level l     -> levelTm    <$> normalise' l
  Lam h b     -> Lam h      <$> normalise' b
  Sort s      -> Sort       <$> normalise' s
  Pi a b      -> uncurry Pi <$> normalise' (a, b)
  DontCare _  -> return v
  Dummy{}     -> return v

-- Note: not the default instance for Elim' since we do something special for Arg.
instance Normalise t => Normalise (Elim' t) where
  normalise' (Apply v) = Apply <$> normalise' v  -- invokes Normalise Arg here
  normalise' (Proj o f)= pure $ Proj o f
  normalise' (IApply x y v) = IApply <$> normalise' x <*> normalise' y <*> normalise' v

instance Normalise Level where
  normalise' (Max m as) = levelMax m <$> normalise' as

instance Normalise PlusLevel where
  normalise' (Plus n l) = Plus n <$> normalise' l

instance Normalise LevelAtom where
  normalise' l = do
    l <- reduce' l
    case l of
      MetaLevel m vs   -> MetaLevel m <$> normalise' vs
      BlockedLevel m v -> BlockedLevel m <$> normalise' v
      NeutralLevel r v -> NeutralLevel r <$> normalise' v
      UnreducedLevel v -> UnreducedLevel <$> normalise' v

instance (Subst t a, Normalise a) => Normalise (Abs a) where
    normalise' a@(Abs x _) = Abs x <$> underAbstraction_ a normalise'
    normalise' (NoAbs x v) = NoAbs x <$> normalise' v

instance Normalise t => Normalise (Arg t) where
    normalise' a
      | isIrrelevant a = return a -- Andreas, 2012-04-02: Do not normalize irrelevant terms!?
      | otherwise      = traverse normalise' a

instance Normalise t => Normalise (Dom t) where
    normalise' = traverse normalise'

instance Normalise a => Normalise (Closure a) where
    normalise' cl = do
        x <- enterClosure cl normalise'
        return $ cl { clValue = x }

instance (Subst t a, Normalise a) => Normalise (Tele a) where
  normalise' EmptyTel        = return EmptyTel
  normalise' (ExtendTel a b) = uncurry ExtendTel <$> normalise' (a, b)

instance Normalise ProblemConstraint where
  normalise' (PConstr pid unblock c) = PConstr pid unblock <$> normalise' c

class NormaliseHet a where
  normaliseHet' :: ContextHet -> a -> ReduceM a
  default normaliseHet' :: (Traversable t, a ~ t b, NormaliseHet b) => ContextHet -> a -> ReduceM a
  normaliseHet' = traverse . normaliseHet'

instance NormaliseHet TwinT where
  normaliseHet' :: ContextHet -> TwinT -> ReduceM TwinT
  normaliseHet' tel (SingleT a) = SingleT <$> underHet @'Both tel normalise' a
  normaliseHet' tel t@(TwinT{necessary,twinPid,twinLHS,twinRHS,twinCompat}) = do
    twinLHS <- underHet @'LHS tel normalise' twinLHS
    twinRHS <- underHet @'RHS tel normalise' twinRHS
    twinCompat <- underHet @'Compat tel normalise' twinCompat
    return TwinT{necessary,twinPid,twinLHS,twinRHS,twinCompat}

-- 2020-07-07 TODO Make more efficient, or give up on names altogether
-- instance {-# OVERLAPPING #-} NormaliseHet ContextHet where
--   normaliseHet' env = go (telToList env)
--     where
--       go :: [Dom (ArgName, TwinT)] -> ContextHet -> ReduceM ContextHet
--       go env EmptyTel = return EmptyTel
--       go env (ExtendTel a (Abs x tel)) = ExtendTel <$> normaliseHet' (telFromList env) a <*> (Abs x <$> go (env ++ [fmap (x,) a]) tel)
--       go env (ExtendTel a (NoAbs{}))   = __IMPOSSIBLE__

instance NormaliseHet a => NormaliseHet (Dom a)
instance NormaliseHet a => NormaliseHet (CompareAs' a)

instance (Sing s, HetSideIsType s ~ 'True, Normalise a) => NormaliseHet (Het s a) where
  normaliseHet' tel a = underHet @s tel normalise' a

instance {-# OVERLAPPING #-} (NormaliseHet a) => NormaliseHet (Het 'Whole a)

instance Normalise ContextHet where
  normalise' = go Empty
    where
      go env Empty = return Empty
      go env (x@(n, v) :<| vs) = (:<|) <$> ((n,) <$> normaliseHet' env v) <*> (go (env :|> x) vs)

instance Normalise Constraint where
  normalise' (ValueCmp cmp t u v) = do
    (t,u,v) <- normalise' (t,u,v)
    return $ ValueCmp cmp t u v
  normalise' (ValueCmpHet cmp tel t u v) = do
    -- 2020-07-07 TODO <victor> Should one normalise the heterogeneous context?
    tel <- normalise' tel
    t' <- normaliseHet' tel t
    u' <- normaliseHet' tel u
    v' <- normaliseHet' tel v
    return $ ValueCmpHet cmp tel t' u' v'
  normalise' (ValueCmpOnFace cmp p t u v) = do
    ((p,t),u,v) <- normalise' ((p,t),u,v)
    return $ ValueCmpOnFace cmp p t u v
  normalise' (ElimCmp cmp fs t v as bs) =
    ElimCmp cmp fs <$> normalise' t <*> normalise' v <*> normalise' as <*> normalise' bs
  normalise' (ElimCmpHet ctx cmp fs t as bs) =
    ElimCmpHet <$> normalise' ctx <*>
      pure cmp <*> pure fs <*> normaliseHet' ctx t <*> normaliseHet' ctx as <*> normaliseHet' ctx bs
  normalise' (LevelCmp cmp u v)    = uncurry (LevelCmp cmp) <$> normalise' (u,v)
  normalise' (TelCmp a b cmp tela telb) = uncurry (TelCmp a b cmp) <$> normalise' (tela,telb)
  normalise' (TelCmpHet ctx a b cmp tela telb) =
    TelCmpHet <$> normalise' ctx <*> pure a <*> pure b <*> pure cmp <*> normaliseHet' ctx tela <*> normaliseHet' ctx telb
  normalise' (SortCmp cmp a b)     = uncurry (SortCmp cmp) <$> normalise' (a,b)
  normalise' (Guarded c pid)       = Guarded <$> normalise' c <*> pure pid
  normalise' (UnBlock m)           = return $ UnBlock m
  normalise' (FindInstance m b cands) = FindInstance m b <$> mapM normalise' cands
  normalise' (IsEmpty r t)         = IsEmpty r <$> normalise' t
  normalise' (CheckSizeLtSat t)    = CheckSizeLtSat <$> normalise' t
  normalise' c@CheckFunDef{}       = return c
  normalise' (HasBiggerSort a)     = HasBiggerSort <$> normalise' a
  normalise' (HasPTSRule a b)      = uncurry HasPTSRule <$> normalise' (a,b)
  normalise' (UnquoteTactic t h g) = UnquoteTactic <$> normalise' t <*> normalise' h <*> normalise' g
  normalise' c@CheckMetaInst{}     = return c

instance Normalise TwinT where
  normalise' = traverse normalise'

instance Normalise CompareAs where
  normalise' = traverse normalise'

instance Normalise ConPatternInfo where
  normalise' i = normalise' (conPType i) <&> \ t -> i { conPType = t }

instance Normalise a => Normalise (Pattern' a) where
  normalise' p = case p of
    VarP o x     -> VarP o <$> normalise' x
    LitP{}       -> return p
    ConP c mt ps -> ConP c <$> normalise' mt <*> normalise' ps
    DefP o q ps  -> DefP o q <$> normalise' ps
    DotP o v     -> DotP o <$> normalise' v
    ProjP{}      -> return p
    IApplyP o t u x -> IApplyP o <$> normalise' t <*> normalise' u <*> normalise' x

instance Normalise DisplayForm where
  normalise' (Display n ps v) = Display n <$> normalise' ps <*> return v

instance Normalise Candidate where
  normalise' (Candidate q u t ov) = Candidate q <$> normalise' u <*> normalise' t <*> pure ov

instance Normalise EqualityView where
  normalise' (OtherType t)            = OtherType
    <$> normalise' t
  normalise' (EqualityType s eq l t a b) = EqualityType
    <$> normalise' s
    <*> return eq
    <*> mapM normalise' l
    <*> normalise' t
    <*> normalise' a
    <*> normalise' b

---------------------------------------------------------------------------
-- * Full instantiation
---------------------------------------------------------------------------

-- | @instantiateFull'@ 'instantiate's metas everywhere (and recursively)
--   but does not 'reduce'.
class InstantiateFull t where
  instantiateFull' :: t -> ReduceM t

  default instantiateFull' :: (t ~ f a, Traversable f, InstantiateFull a) => t -> ReduceM t
  instantiateFull' = traverse instantiateFull'

-- Traversables (doesn't include binders like Abs, Tele):

instance InstantiateFull t => InstantiateFull [t]
instance InstantiateFull t => InstantiateFull (HashMap k t)
instance InstantiateFull t => InstantiateFull (Map k t)
instance InstantiateFull t => InstantiateFull (Maybe t)
instance InstantiateFull t => InstantiateFull (Strict.Maybe t)

instance InstantiateFull t => InstantiateFull (Arg t)
instance InstantiateFull t => InstantiateFull (Elim' t)
instance InstantiateFull t => InstantiateFull (Named name t)
instance InstantiateFull t => InstantiateFull (Open t)
instance InstantiateFull t => InstantiateFull (WithArity t)

-- Tuples:

instance (InstantiateFull a, InstantiateFull b) => InstantiateFull (a,b) where
    instantiateFull' (x,y) = (,) <$> instantiateFull' x <*> instantiateFull' y

instance (InstantiateFull a, InstantiateFull b, InstantiateFull c) => InstantiateFull (a,b,c) where
    instantiateFull' (x,y,z) =
        do  (x,(y,z)) <- instantiateFull' (x,(y,z))
            return (x,y,z)

instance (InstantiateFull a, InstantiateFull b, InstantiateFull c, InstantiateFull d) => InstantiateFull (a,b,c,d) where
    instantiateFull' (x,y,z,w) =
        do  (x,(y,z,w)) <- instantiateFull' (x,(y,z,w))
            return (x,y,z,w)

-- Base types:

instance InstantiateFull Bool where
    instantiateFull' = return

instance InstantiateFull Char where
    instantiateFull' = return

instance InstantiateFull Int where
    instantiateFull' = return

instance InstantiateFull ModuleName where
    instantiateFull' = return

instance InstantiateFull Name where
    instantiateFull' = return

instance InstantiateFull QName where
  instantiateFull' = return

instance InstantiateFull Scope where
    instantiateFull' = return

instance InstantiateFull ConHead where
  instantiateFull' = return

instance InstantiateFull DBPatVar where
    instantiateFull' = return

-- Rest:

instance InstantiateFull Sort where
    instantiateFull' s = do
        s <- instantiate' s
        case s of
            Type n     -> Type <$> instantiateFull' n
            Prop n     -> Prop <$> instantiateFull' n
            PiSort a s -> piSort <$> instantiateFull' a <*> instantiateFull' s
            FunSort s1 s2 -> funSort <$> instantiateFull' s1 <*> instantiateFull' s2
            UnivSort s -> univSort <$> instantiateFull' s
            Inf _      -> return s
            SizeUniv   -> return s
            MetaS x es -> MetaS x <$> instantiateFull' es
            DefS d es  -> DefS d <$> instantiateFull' es
            DummyS{}   -> return s

instance InstantiateFull t => InstantiateFull (Type' t) where
    instantiateFull' (El s t) =
      El <$> instantiateFull' s <*> instantiateFull' t

instance InstantiateFull Term where
    instantiateFull' v = etaOnce =<< do -- Andreas, 2010-11-12 DONT ETA!? eta-reduction breaks subject reduction
-- but removing etaOnce now breaks everything
      v <- instantiate' v
      case v of
          Var n vs    -> Var n <$> instantiateFull' vs
          Con c ci vs -> Con c ci <$> instantiateFull' vs
          Def f vs    -> Def f <$> instantiateFull' vs
          MetaV x vs  -> MetaV x <$> instantiateFull' vs
          Lit _       -> return v
          Level l     -> levelTm <$> instantiateFull' l
          Lam h b     -> Lam h <$> instantiateFull' b
          Sort s      -> Sort <$> instantiateFull' s
          Pi a b      -> uncurry Pi <$> instantiateFull' (a,b)
          DontCare v  -> dontCare <$> instantiateFull' v
          Dummy{}     -> return v

instance InstantiateFull Level where
  instantiateFull' (Max m as) = levelMax m <$> instantiateFull' as

instance InstantiateFull PlusLevel where
  instantiateFull' (Plus n l) = Plus n <$> instantiateFull' l

instance InstantiateFull LevelAtom where
  instantiateFull' l = case l of
    MetaLevel m vs -> do
      v <- instantiateFull' (MetaV m vs)
      case v of
        MetaV m vs -> return $ MetaLevel m vs
        _          -> return $ UnreducedLevel v
    NeutralLevel r v -> NeutralLevel r <$> instantiateFull' v
    BlockedLevel b v -> instantiate' b >>= \ case
      b | b == alwaysUnblock -> UnreducedLevel <$> instantiateFull' v
        | otherwise          -> BlockedLevel b <$> instantiateFull' v
    UnreducedLevel v -> UnreducedLevel <$> instantiateFull' v

instance InstantiateFull Substitution where
  instantiateFull' sigma =
    case sigma of
      IdS                  -> return IdS
      EmptyS err           -> return $ EmptyS err
      Wk   n sigma         -> Wk   n         <$> instantiateFull' sigma
      Lift n sigma         -> Lift n         <$> instantiateFull' sigma
      Strengthen bot sigma -> Strengthen bot <$> instantiateFull' sigma
      t :# sigma           -> consS <$> instantiateFull' t
                                    <*> instantiateFull' sigma

instance InstantiateFull ConPatternInfo where
    instantiateFull' i = instantiateFull' (conPType i) <&> \ t -> i { conPType = t }

instance InstantiateFull a => InstantiateFull (Pattern' a) where
    instantiateFull' (VarP o x)     = VarP o <$> instantiateFull' x
    instantiateFull' (DotP o t)     = DotP o <$> instantiateFull' t
    instantiateFull' (ConP n mt ps) = ConP n <$> instantiateFull' mt <*> instantiateFull' ps
    instantiateFull' (DefP o q ps) = DefP o q <$> instantiateFull' ps
    instantiateFull' l@LitP{}       = return l
    instantiateFull' p@ProjP{}      = return p
    instantiateFull' (IApplyP o t u x) = IApplyP o <$> instantiateFull' t <*> instantiateFull' u <*> instantiateFull' x

instance (Subst t a, InstantiateFull a) => InstantiateFull (Abs a) where
    instantiateFull' a@(Abs x _) = Abs x <$> underAbstraction_ a instantiateFull'
    instantiateFull' (NoAbs x a) = NoAbs x <$> instantiateFull' a

instance (InstantiateFull t, InstantiateFull e) => InstantiateFull (Dom' t e) where
    instantiateFull' (Dom i fin n tac x) = Dom i fin n <$> instantiateFull' tac <*> instantiateFull' x

instance InstantiateFull a => InstantiateFull (Closure a) where
    instantiateFull' cl = do
        x <- enterClosure cl instantiateFull'
        return $ cl { clValue = x }

instance InstantiateFull ProblemConstraint where
  instantiateFull' (PConstr p u c) = PConstr p u <$> instantiateFull' c

class InstantiateFullHet a where
  instantiateFullHet' :: ContextHet -> a -> ReduceM a
  default instantiateFullHet' :: (Traversable t, a ~ t b, InstantiateFullHet b) => ContextHet -> a -> ReduceM a
  instantiateFullHet' = traverse . instantiateFullHet'

instance InstantiateFullHet TwinT where
  instantiateFullHet' :: ContextHet -> TwinT -> ReduceM TwinT
  instantiateFullHet' tel (SingleT a) = SingleT <$> underHet @'Both tel instantiateFull' a
  instantiateFullHet' tel t@(TwinT{necessary,twinPid,twinLHS,twinRHS,twinCompat}) = do
    twinLHS <- underHet @'LHS tel instantiateFull' twinLHS
    twinRHS <- underHet @'RHS tel instantiateFull' twinRHS
    twinCompat <- underHet @'Compat tel instantiateFull' twinCompat
    return TwinT{necessary,twinPid,twinLHS,twinRHS,twinCompat}

instance {-# OVERLAPPING #-} InstantiateFullHet a => InstantiateFullHet (Het 'Whole a)

-- 2020-07-07 TODO Make more efficient, or give up on names altogether
-- instance InstantiateFullHet ContextHet where
--   instantiateFullHet' env = go (telToList env)
--     where
--       go :: [Dom (ArgName, TwinT)] -> ContextHet -> ReduceM ContextHet
--       go env EmptyTel = return EmptyTel
--       go env (ExtendTel a (Abs x tel)) = ExtendTel <$> instantiateFullHet' (telFromList env) a <*> (Abs x <$> go (env ++ [fmap (x,) a]) tel)
--       go env (ExtendTel a (NoAbs{}))   = __IMPOSSIBLE__

instance InstantiateFullHet a => InstantiateFullHet (Dom a)
instance InstantiateFullHet a => InstantiateFullHet (CompareAs' a)

instance InstantiateFull ContextHet where
  instantiateFull' = go Empty
    where
      go env Empty = return Empty
      go env (x@(n, v) :<| vs) = (:<|) <$> ((n,) <$> instantiateFullHet' env v) <*> (go (env :|> x) vs)

instance (Sing s, HetSideIsType s ~ 'True, InstantiateFull a) => InstantiateFullHet (Het s a) where
  instantiateFullHet' tel a = underHet @s tel instantiateFull' a

instance InstantiateFull Constraint where
  instantiateFull' c = case c of
    ValueCmp cmp t u v -> do
      (t,u,v) <- instantiateFull' (t,u,v)
      return $ ValueCmp cmp t u v
    ValueCmpHet cmp tel t u v -> do
      -- 2020-07-07 TODO <victor> Should one reduce the telescope?
      tel <- instantiateFull' tel
      t' <- instantiateFullHet' tel t
      u' <- instantiateFullHet' tel u
      v' <- instantiateFullHet' tel v
      return $ ValueCmpHet cmp tel t' u' v'
    ValueCmpOnFace cmp p t u v -> do
      ((p,t),u,v) <- instantiateFull' ((p,t),u,v)
      return $ ValueCmpOnFace cmp p t u v
    ElimCmp cmp fs t v as bs ->
      ElimCmp cmp fs <$> instantiateFull' t <*> instantiateFull' v <*> instantiateFull' as <*> instantiateFull' bs
    ElimCmpHet ctx cmp fs t as bs ->
      ElimCmpHet <$> instantiateFull' ctx <*>
        pure cmp <*> pure fs <*> instantiateFullHet' ctx t <*> instantiateFullHet' ctx as <*> instantiateFullHet' ctx bs
    LevelCmp cmp u v    -> uncurry (LevelCmp cmp) <$> instantiateFull' (u,v)
    TelCmp a b cmp tela telb -> uncurry (TelCmp a b cmp) <$> instantiateFull' (tela,telb)
    TelCmpHet ctx a b cmp tela telb ->
      TelCmpHet <$> instantiateFull' ctx <*>
        pure a <*> pure b <*> pure cmp <*> instantiateFullHet' ctx tela <*> instantiateFullHet' ctx telb
    SortCmp cmp a b     -> uncurry (SortCmp cmp) <$> instantiateFull' (a,b)
    Guarded c pid       -> Guarded <$> instantiateFull' c <*> pure pid
    UnBlock m           -> return $ UnBlock m
    FindInstance m b cands -> FindInstance m b <$> mapM instantiateFull' cands
    IsEmpty r t         -> IsEmpty r <$> instantiateFull' t
    CheckSizeLtSat t    -> CheckSizeLtSat <$> instantiateFull' t
    c@CheckFunDef{}     -> return c
    HasBiggerSort a     -> HasBiggerSort <$> instantiateFull' a
    HasPTSRule a b      -> uncurry HasPTSRule <$> instantiateFull' (a,b)
    UnquoteTactic t g h -> UnquoteTactic <$> instantiateFull' t <*> instantiateFull' g <*> instantiateFull' h
    c@CheckMetaInst{}   -> return c

instance InstantiateFull TwinT where

instance InstantiateFull a => InstantiateFull (CompareAs' a) where

instance InstantiateFull Signature where
  instantiateFull' (Sig a b c) = uncurry3 Sig <$> instantiateFull' (a, b, c)

instance InstantiateFull Section where
  instantiateFull' (Section tel) = Section <$> instantiateFull' tel

instance (Subst t a, InstantiateFull a) => InstantiateFull (Tele a) where
  instantiateFull' EmptyTel = return EmptyTel
  instantiateFull' (ExtendTel a b) = uncurry ExtendTel <$> instantiateFull' (a, b)

instance InstantiateFull Definition where
    instantiateFull' def@Defn{ defType = t ,defDisplay = df, theDef = d } = do
      (t, df, d) <- instantiateFull' (t, df, d)
      return $ def{ defType = t, defDisplay = df, theDef = d }

instance InstantiateFull NLPat where
  instantiateFull' (PVar x y) = return $ PVar x y
  instantiateFull' (PDef x y) = PDef <$> instantiateFull' x <*> instantiateFull' y
  instantiateFull' (PLam x y) = PLam x <$> instantiateFull' y
  instantiateFull' (PPi x y)  = PPi <$> instantiateFull' x <*> instantiateFull' y
  instantiateFull' (PSort x)  = PSort <$> instantiateFull' x
  instantiateFull' (PBoundVar x y) = PBoundVar x <$> instantiateFull' y
  instantiateFull' (PTerm x)  = PTerm <$> instantiateFull' x

instance InstantiateFull NLPType where
  instantiateFull' (NLPType s a) = NLPType
    <$> instantiateFull' s
    <*> instantiateFull' a

instance InstantiateFull NLPSort where
  instantiateFull' (PType x) = PType <$> instantiateFull' x
  instantiateFull' (PProp x) = PProp <$> instantiateFull' x
  instantiateFull' (PInf n)  = return $ PInf n
  instantiateFull' PSizeUniv = return PSizeUniv

instance InstantiateFull RewriteRule where
  instantiateFull' (RewriteRule q gamma f ps rhs t) =
    RewriteRule q
      <$> instantiateFull' gamma
      <*> pure f
      <*> instantiateFull' ps
      <*> instantiateFull' rhs
      <*> instantiateFull' t

instance InstantiateFull DisplayForm where
  instantiateFull' (Display n ps v) = uncurry (Display n) <$> instantiateFull' (ps, v)

instance InstantiateFull DisplayTerm where
  instantiateFull' (DTerm v)       = DTerm <$> instantiateFull' v
  instantiateFull' (DDot  v)       = DDot  <$> instantiateFull' v
  instantiateFull' (DCon c ci vs)  = DCon c ci <$> instantiateFull' vs
  instantiateFull' (DDef c es)     = DDef c <$> instantiateFull' es
  instantiateFull' (DWithApp v vs ws) = uncurry3 DWithApp <$> instantiateFull' (v, vs, ws)

instance InstantiateFull Defn where
    instantiateFull' d = case d of
      Axiom{} -> return d
      DataOrRecSig{} -> return d
      GeneralizableVar{} -> return d
      AbstractDefn d -> AbstractDefn <$> instantiateFull' d
      Function{ funClauses = cs, funCompiled = cc, funCovering = cov, funInv = inv, funExtLam = extLam } -> do
        (cs, cc, cov, inv) <- instantiateFull' (cs, cc, cov, inv)
        extLam <- instantiateFull' extLam
        return $ d { funClauses = cs, funCompiled = cc, funCovering = cov, funInv = inv, funExtLam = extLam }
      Datatype{ dataSort = s, dataClause = cl } -> do
        s  <- instantiateFull' s
        cl <- instantiateFull' cl
        return $ d { dataSort = s, dataClause = cl }
      Record{ recClause = cl, recTel = tel } -> do
        cl  <- instantiateFull' cl
        tel <- instantiateFull' tel
        return $ d { recClause = cl, recTel = tel }
      Constructor{} -> return d
      Primitive{ primClauses = cs } -> do
        cs <- instantiateFull' cs
        return $ d { primClauses = cs }
      PrimitiveSort{} -> return d

instance InstantiateFull ExtLamInfo where
  instantiateFull' e@(ExtLamInfo { extLamSys = sys}) = do
    sys <- instantiateFull' sys
    return $ e { extLamSys = sys}

instance InstantiateFull System where
  instantiateFull' (System tel sys) = System <$> instantiateFull' tel <*> instantiateFull' sys

instance InstantiateFull FunctionInverse where
  instantiateFull' NotInjective = return NotInjective
  instantiateFull' (Inverse inv) = Inverse <$> instantiateFull' inv

instance InstantiateFull a => InstantiateFull (Case a) where
  instantiateFull' (Branches cop cs eta ls m b lz) =
    Branches cop
      <$> instantiateFull' cs
      <*> instantiateFull' eta
      <*> instantiateFull' ls
      <*> instantiateFull' m
      <*> pure b
      <*> pure lz

instance InstantiateFull CompiledClauses where
  instantiateFull' Fail        = return Fail
  instantiateFull' (Done m t)  = Done m <$> instantiateFull' t
  instantiateFull' (Case n bs) = Case n <$> instantiateFull' bs

instance InstantiateFull Clause where
    instantiateFull' (Clause rl rf tel ps b t catchall recursive unreachable ell) =
       Clause rl rf <$> instantiateFull' tel
       <*> instantiateFull' ps
       <*> instantiateFull' b
       <*> instantiateFull' t
       <*> return catchall
       <*> return recursive
       <*> return unreachable
       <*> return ell

instance InstantiateFull Interface where
    instantiateFull' (Interface h s ft ms mod scope inside
                               sig display userwarn importwarn b foreignCode
                               highlighting pragmas usedOpts patsyns warnings partialdefs) =
        Interface h s ft ms mod scope inside
            <$> instantiateFull' sig
            <*> instantiateFull' display
            <*> return userwarn
            <*> return importwarn
            <*> instantiateFull' b
            <*> return foreignCode
            <*> return highlighting
            <*> return pragmas
            <*> return usedOpts
            <*> return patsyns
            <*> return warnings
            <*> return partialdefs

instance InstantiateFull a => InstantiateFull (Builtin a) where
    instantiateFull' (Builtin t) = Builtin <$> instantiateFull' t
    instantiateFull' (Prim x)   = Prim <$> instantiateFull' x

instance InstantiateFull Candidate where
  instantiateFull' (Candidate q u t ov) =
    Candidate q <$> instantiateFull' u <*> instantiateFull' t <*> pure ov

instance InstantiateFull EqualityView where
  instantiateFull' (OtherType t)            = OtherType
    <$> instantiateFull' t
  instantiateFull' (EqualityType s eq l t a b) = EqualityType
    <$> instantiateFull' s
    <*> return eq
    <*> mapM instantiateFull' l
    <*> instantiateFull' t
    <*> instantiateFull' a
    <*> instantiateFull' b
