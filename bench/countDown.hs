{-# LANGUAGE DataKinds, DeriveFunctor, FlexibleContexts, GADTs, LambdaCase, RankNTypes, ScopedTypeVariables, TypeOperators #-}
module Main (main) where

import qualified Control.Monad.Except as MTL
import qualified Control.Monad.State as MTL
import qualified Control.Monad.Free as Free

import Control.Monad
import Criterion (bench, bgroup, whnf)
import Criterion.Main (defaultMain)
import Data.Functor.Identity

import qualified Control.Monad.Freer as Simple
import qualified Control.Monad.Freer.State as Simple

import qualified Lib as TFTF
import qualified Eff.Type as TFTF

--------------------------------------------------------------------------------
                        -- State Benchmarks --
--------------------------------------------------------------------------------

countDown :: Int -> (Int, Int)
countDown start = Simple.run (Simple.runState start go)
  where
    go :: Simple.Eff '[Simple.State Int] Int
    go = Simple.get >>= (\n -> if n <= 0 then pure n else Simple.put (n-1) >> go)

countDownMTL :: Int -> (Int, Int)
countDownMTL = MTL.runState go
  where
    go :: MTL.State Int Int
    go = MTL.get >>= (\n -> if n <= 0 then pure n else MTL.put (n-1) >> go)

countDownTFTF :: Int -> Int
countDownTFTF start = fst $ TFTF.run $ TFTF.runState start go
  where
    go :: TFTF.Eff '[TFTF.State Int, Identity] Int
    go = TFTF.get >>= (\n -> if n <= 0 then (pure n) else (TFTF.put (n-1)) >> go)


--------------------------------------------------------------------------------
-- A version of too-fast-too-free which isn't micro-optimized, because I want to
-- compare the two approaches but I don't want to spend days staring at core.
--------------------------------------------------------------------------------

newtype FreerFinal g a = FreerFinal
  { runFreerFinal :: forall m. Monad m
                  => (forall t. g t -> m t)
                  -> m a
  }

instance Functor (FreerFinal g) where
  fmap f fa = FreerFinal $ \embed -> do
    f <$> runFreerFinal fa embed

instance Applicative (FreerFinal g) where
  pure x = FreerFinal (\_ -> pure x)
  (<*>) = ap

instance Monad (FreerFinal g) where
  fa >>= cc = FreerFinal $ \embed -> do
    a <- runFreerFinal fa embed
    runFreerFinal (cc a) embed

embedInFinal :: g a -> FreerFinal g a
embedInFinal ga = FreerFinal $ \embed -> embed ga

data StateG s a where
  GetG :: StateG s s
  PutG :: s -> StateG s ()

runStateFinal :: forall s a. s -> FreerFinal (StateG s) a -> FreerFinal Identity (a, s)
runStateFinal s0 fa = flip MTL.runStateT s0 $ runFreerFinal fa embed
  where
    embed :: StateG s x -> MTL.StateT s (FreerFinal Identity) x
    embed GetG      = MTL.get
    embed (PutG s') = MTL.put s'

runIdentityFinal :: FreerFinal Identity a -> a
runIdentityFinal fa = runIdentity $ runFreerFinal fa id

countDownFinal :: Int -> Int
countDownFinal start = fst $ runIdentityFinal $ runStateFinal start go
  where
    go :: FreerFinal (StateG Int) Int
    go = embedInFinal GetG >>= (\n -> if n <= 0 then (pure n) else embedInFinal (PutG (n-1)) >> go)


--------------------------------------------------------------------------------
-- Free
--------------------------------------------------------------------------------

data Free f a
  = Pure a
  | Deep (f (Free f a))

instance Functor f => Functor (Free f) where
  fmap f (Pure a)   = Pure (f a)
  fmap f (Deep ffa) = Deep (fmap (fmap f) ffa)

instance Functor f => Applicative (Free f) where
  pure = Pure
  (<*>) = ap

instance Functor f => Monad (Free f) where
  Pure a   >>= cc = cc a
  Deep ffa >>= cc = Deep (fmap (>>= cc) ffa)

embedInFree :: Functor f => f a -> Free f a
embedInFree fa = Deep (fmap Pure fa)

data StateF s a = GetF (s -> a) | PutF s a
  deriving Functor

runStateFree :: forall s a. s -> Free (StateF s) a -> Free Identity (a, s)
runStateFree s0 = flip MTL.runStateT s0 . go
  where
    go :: Free (StateF s) x -> MTL.StateT s (Free Identity) x
    go (Pure x) = pure x
    go (Deep (GetF cc)) = do s <- MTL.get
                             go (cc s)
    go (Deep (PutF s' fx)) = do MTL.put s'
                                go fx

runIdentityFree :: Free Identity a -> a
runIdentityFree (Pure a) = a
runIdentityFree (Deep (Identity fa)) = runIdentityFree fa

countDownFree :: Int -> Int
countDownFree start = fst $ runIdentityFree $ runStateFree start go
  where
    go :: Free (StateF Int) Int
    go = embedInFree (GetF id) >>= (\n -> if n <= 0 then (pure n) else embedInFree (PutF (n-1) ()) >> go)


--------------------------------------------------------------------------------
-- Freer
--------------------------------------------------------------------------------

data Freer g a where
  Purer  :: a -> Freer g a
  Deeper :: g x -> (x -> Freer g a) -> Freer g a

instance Functor (Freer g) where
  fmap f (Purer a)      = Purer (f a)
  fmap f (Deeper gx cc) = Deeper gx (fmap (fmap f) cc)

instance Applicative (Freer g) where
  pure = Purer
  (<*>) = ap

instance Monad (Freer g) where
  Purer a      >>= cc' = cc' a
  Deeper gx cc >>= cc' = Deeper gx (fmap (>>= cc') cc)

embedInFreer :: g a -> Freer g a
embedInFreer ga = Deeper ga Purer

runStateFreer :: forall s a. s -> Freer (StateG s) a -> Freer Identity (a, s)
runStateFreer s0 = flip MTL.runStateT s0 . go
  where
    go :: Freer (StateG s) x -> MTL.StateT s (Freer Identity) x
    go (Purer x) = pure x
    go (Deeper GetG cc) = do s <- MTL.get
                             go (cc s)
    go (Deeper (PutG s') cc) = do MTL.put s'
                                  go (cc ())

runIdentityFreer :: Freer Identity a -> a
runIdentityFreer (Purer a) = a
runIdentityFreer (Deeper (Identity x) cc) = runIdentityFreer (cc x)

countDownFreer :: Int -> Int
countDownFreer start = fst $ runIdentityFreer $ runStateFreer start go
  where
    go :: Freer (StateG Int) Int
    go = embedInFreer GetG >>= (\n -> if n <= 0 then (pure n) else embedInFreer (PutG (n-1)) >> go)


--------------------------------------------------------------------------------
-- Ran + Freer (the difference list trick applied to (>>=))
--------------------------------------------------------------------------------

newtype Codensity m a = Codensity
  { unCodensity :: forall b. (a -> m b) -> m b
  }

instance Functor (Codensity m) where
  fmap f ca = Codensity $ \embedB -> do
    unCodensity ca $ \a -> do
      embedB (f a)

instance Applicative (Codensity m) where
  pure a = Codensity $ \embed -> embed a
  (<*>) = ap

instance Monad (Codensity m) where
  ca >>= cc = Codensity $ \embedB -> do
    unCodensity ca $ \a -> unCodensity (cc a) embedB

embedInCodensity :: Monad m => m a -> Codensity m a
embedInCodensity ma = Codensity $ \embed -> do
  a <- ma
  embed a

runCodensity :: Monad m => Codensity m a -> m a
runCodensity ca = unCodensity ca pure


type Codenser g = Codensity (Freer g)

embedInCodenser :: g a -> Codenser g a
embedInCodenser = embedInCodensity . embedInFreer

runStateCodenser :: forall s a. s -> Codenser (StateG s) a -> Codenser Identity (a, s)
runStateCodenser s0 = flip MTL.runStateT s0 . go . runCodensity
  where
    go :: Freer (StateG s) x -> MTL.StateT s (Codenser Identity) x
    go (Purer x) = pure x
    go (Deeper GetG cc) = do s <- MTL.get
                             go (cc s)
    go (Deeper (PutG s') cc) = do MTL.put s'
                                  go (cc ())

runIdentityCodenser :: Codenser Identity a -> a
runIdentityCodenser = runIdentityFreer . runCodensity

countDownCodenser :: Int -> Int
countDownCodenser start = fst $ runIdentityCodenser $ runStateCodenser start go
  where
    go :: Codenser (StateG Int) Int
    go = embedInCodenser GetG >>= (\n -> if n <= 0 then (pure n) else embedInCodenser (PutG (n-1)) >> go)


main :: IO ()
main =
  defaultMain [
    bgroup "Countdown Bench" [
        bench "freer-simple"      $ whnf countDown 10000
      , bench "mtl"               $ whnf countDownMTL 10000
      , bench "too-fast-too-free" $ whnf countDownTFTF 10000
      , bench "final-encoding"    $ whnf countDownFinal 10000
      , bench "Free"              $ whnf countDownFree 10000
      , bench "Freer"             $ whnf countDownFreer 10000
      , bench "Codensity+Freer"   $ whnf countDownCodenser 10000
    ]
  ]
