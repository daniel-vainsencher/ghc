%
% (c) The AQUA Project, Glasgow University, 1993-1998
%
\section[SimplMonad]{The simplifier Monad}

\begin{code}
module SimplMonad (
        -- The monad
        SimplM,
        initSmpl,
        getSimplRules, getFamEnvs,

        -- Unique supply
        MonadUnique(..), newId,
        -- Tape access
        gotTape, tapeLeft, consumeDecision,

        -- Counting
        SimplCount, tick, freeTick, checkedTick,
        getSimplCount, zeroSimplCount, pprSimplCount,
        plusSimplCount, isZeroSimplCount
    ) where

import Id               ( Id, mkSysLocal )
import Type             ( Type )
import FamInstEnv       ( FamInstEnv )
import Rules            ( RuleBase )
import UniqSupply
import DynFlags
import CoreMonad
import Outputable
import FastString
import MonadUtils
\end{code}

%************************************************************************
%*                                                                      *
\subsection{Monad plumbing}
%*                                                                      *
%************************************************************************

For the simplifier monad, we want to {\em thread} a unique supply and a counter.
(Command-line switches move around through the explicitly-passed SimplEnv.)

\begin{code}
newtype SimplM result
  =  SM  { unSM :: SimplTopEnv  -- Envt that does not change much
                -> UniqSupply   -- We thread the unique supply because
                                -- constantly splitting it is rather expensive
                -> MTape
                -> SimplCount
                -> IO (result, UniqSupply, MTape, SimplCount)}
  -- we only need IO here for dump output

data SimplTopEnv
  = STE { st_flags :: DynFlags
        , st_max_ticks :: Int  -- Max #ticks in this simplifier run
                               -- Zero means infinity!
        , st_rules :: RuleBase
        , st_fams  :: (FamInstEnv, FamInstEnv) }
\end{code}

\begin{code}
initSmpl :: DynFlags -> RuleBase -> (FamInstEnv, FamInstEnv)
         -> UniqSupply          -- No init count; set to 0
         -> MTape
         -> Int                 -- Size of the bindings, used to limit
                                -- the number of ticks we allow
         -> SimplM a
         -> IO (a, SimplCount)

initSmpl dflags rules fam_envs us tape size m
  = do (result, _, _, count) <- unSM m env us tape (zeroSimplCount dflags)
       return (result, count)
  where
    env = STE { st_flags = dflags, st_rules = rules
              , st_max_ticks = computeMaxTicks dflags size
              , st_fams = fam_envs }

computeMaxTicks :: DynFlags -> Int -> Int
-- Compute the max simplifier ticks as
--     (base-size + pgm-size) * magic-multiplier * tick-factor/100
-- where
--    magic-multiplier is a constant that gives reasonable results
--    base-size is a constant to deal with size-zero programs
computeMaxTicks dflags size
  = fromInteger ((toInteger (size + base_size)
                  * toInteger (tick_factor * magic_multiplier))
          `div` 100)
  where
    tick_factor      = simplTickFactor dflags
    base_size        = 100
    magic_multiplier = 40
        -- MAGIC NUMBER, multiplies the simplTickFactor
        -- We can afford to be generous; this is really
        -- just checking for loops, and shouldn't usually fire
        -- A figure of 20 was too small: see Trac #553

{-# INLINE thenSmpl #-}
{-# INLINE thenSmpl_ #-}
{-# INLINE returnSmpl #-}

instance Monad SimplM where
   (>>)   = thenSmpl_
   (>>=)  = thenSmpl
   return = returnSmpl

returnSmpl :: a -> SimplM a
returnSmpl e = SM (\_st_env us tape sc -> return (e, us, tape, sc))

thenSmpl  :: SimplM a -> (a -> SimplM b) -> SimplM b
thenSmpl_ :: SimplM a -> SimplM b -> SimplM b

thenSmpl m k
  = SM $ \st_env us0 tape0 sc0 -> do
      (m_result, us1, tape1, sc1) <- unSM m st_env us0 tape0 sc0
      unSM (k m_result) st_env us1 tape1 sc1

thenSmpl_ m k
  = SM $ \st_env us0 tape0 sc0 -> do
      (_, us1, tape1, sc1) <- unSM m st_env us0 tape0 sc0
      unSM k st_env us1 tape1 sc1

-- TODO: this specializing is not allowed
-- {-# SPECIALIZE mapM         :: (a -> SimplM b) -> [a] -> SimplM [b] #-}
-- {-# SPECIALIZE mapAndUnzipM :: (a -> SimplM (b, c)) -> [a] -> SimplM ([b],[c]) #-}
-- {-# SPECIALIZE mapAccumLM   :: (acc -> b -> SimplM (acc,c)) -> acc -> [b] -> SimplM (acc, [c]) #-}
\end{code}


%************************************************************************
%*                                                                      *
\subsection{The unique supply}
%*                                                                      *
%************************************************************************

\begin{code}
instance MonadUnique SimplM where
    getUniqueSupplyM
       = SM (\_st_env us tape sc -> case splitUniqSupply us of
                                (us1, us2) -> return (us1, us2, tape, sc))

    getUniqueM
       = SM (\_st_env us tape sc -> case splitUniqSupply us of
                                (us1, us2) -> return (uniqFromSupply us1, us2, tape, sc))

    getUniquesM
        = SM (\_st_env us tape sc -> case splitUniqSupply us of
                                (us1, us2) -> return (uniqsFromSupply us1, us2, tape, sc))

instance HasDynFlags SimplM where
    getDynFlags = SM (\st_env us tape sc -> return (st_flags st_env, us, tape, sc))

instance MonadIO SimplM where
    liftIO m = SM $ \_ us tape sc -> do
      x <- m
      return (x, us, tape, sc)

getSimplRules :: SimplM RuleBase
getSimplRules = SM (\st_env us tape sc -> return (st_rules st_env, us, tape, sc))

getFamEnvs :: SimplM (FamInstEnv, FamInstEnv)
getFamEnvs = SM (\st_env us tape sc -> return (st_fams st_env, us, tape, sc))

newId :: FastString -> Type -> SimplM Id
newId fs ty = do uniq <- getUniqueM
                 return (mkSysLocal fs uniq ty)
\end{code}

%************************************************************************
%*                                                                      *
\subsection{The tape}
%*                                                                      *
%************************************************************************

\begin{code}
consumeDecision :: SimplM SearchTapeElement
consumeDecision = SM (\_st_env us tape sc -> case tape of
                       Just (te:tes) -> return (te, us, Just tes, sc)
                       otherwise -> error "Ran out of tape early, I don't know what to do")

gotTape :: SimplM Bool
gotTape = SM (\_st_env us tape sc -> case tape of
                       Just t -> return (True, us, tape, sc)
                       otherwise -> return (False, us, tape, sc))

tapeLeft :: SimplM Bool
tapeLeft = SM (\_st_env us tape sc -> case tape of
                       Just (te:tes) -> return (True, us, tape, sc)
                       otherwise -> return (False, us, tape, sc))

\end{code}

%************************************************************************
%*                                                                      *
\subsection{Counting up what we've done}
%*                                                                      *
%************************************************************************

\begin{code}
getSimplCount :: SimplM SimplCount
getSimplCount = SM (\_st_env us tape sc -> return (sc, us, tape, sc))

tick :: Tick -> SimplM ()
tick t = SM (\st_env us tape sc -> let sc' = doSimplTick (st_flags st_env) t sc
                              in sc' `seq` return ((), us, tape, sc'))

checkedTick :: Tick -> SimplM ()
-- Try to take a tick, but fail if too many
checkedTick t
  = SM (\st_env us tape sc -> if st_max_ticks st_env <= simplCountN sc
                         then pprPanic "Simplifier ticks exhausted" (msg sc)
                         else let sc' = doSimplTick (st_flags st_env) t sc
                              in sc' `seq` return ((), us, tape, sc'))
  where
    msg sc = vcat [ ptext (sLit "When trying") <+> ppr t
                  , ptext (sLit "To increase the limit, use -fsimpl-tick-factor=N (default 100)")
                  , ptext (sLit "If you need to do this, let GHC HQ know, and what factor you needed")
                  , pp_details sc
                  , pprSimplCount sc ]
    pp_details sc
      | hasDetailedCounts sc = empty
      | otherwise = ptext (sLit "To see detailed counts use -ddump-simpl-stats")


freeTick :: Tick -> SimplM ()
-- Record a tick, but don't add to the total tick count, which is
-- used to decide when nothing further has happened
freeTick t
   = SM (\_st_env us tape sc -> let sc' = doFreeSimplTick t sc
                           in sc' `seq` return ((), us, tape, sc'))
\end{code}
