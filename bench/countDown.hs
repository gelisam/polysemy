{-# LANGUAGE DataKinds, DeriveFunctor, FlexibleContexts, GADTs, TypeOperators #-}
module Main (main) where

import qualified Control.Monad.Except as MTL
import qualified Control.Monad.State as MTL
import qualified Control.Monad.Free as Free

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


main :: IO ()
main =
  defaultMain [
    bgroup "Countdown Bench" [
        bench "freer-simple"      $ whnf countDown 10000
      , bench "mtl"               $ whnf countDownMTL 10000
      , bench "too-fast-too-free" $ whnf countDownTFTF 10000
    ]
  ]
