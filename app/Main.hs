{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Main (main) where

import Tct.Core
import Tct.Trs
import Tct.Trs.Interactive

import qualified Tct.Trs.Processor.Poly.GUBS as G
import qualified Tct.Trs.Processor.Poly.NaturalPI as P

instance Declared Trs Trs where decls = decls'

main :: IO ()
main = runTrs trsConfig


deg = 4

decls' = 
 (\opts -> SD $ strategy (toName opts) () $ simple (G.gubs opts)) `fmap` options
 ++
 -- [ SD $ strategy "gubs-all"   () $ simple (G.gubs G.defaultGUBSOptions)
 -- , SD $ strategy "gubs-any"   () $ simple (G.gubs G.defaultGUBSOptions)
 -- , SD $ strategy "gubs-one"   () $ simple (G.gubs G.defaultGUBSOptions)
 [ SD $ strategy "slogic-All-Minismt" () $ simple      slogicAll 
 , SD $ strategy "slogic-Any-Minismt" () $ simple (tew slogicAny)
 , SD $ strategy "slogic-All-Z3" () $ withZ3 $ simple      slogicAll 
 , SD $ strategy "slogic-Any-Z3" () $ withZ3 $ simple (tew slogicAny) ]

withZ3 = withKvPair ("solver",["z3","-smt2"])

toName G.GUBSOptions{..} = "gubs-" ++ show selector ++ "-" ++ show smtSolver ++ "-" ++ show scc 

options = 
  [ G.GUBSOptions{..} 
    | let degree = deg
    , selector <- selectors
    , scc <- sccs
    , smtSolver <- solvers
    , let minimize = G.Minimize ]

solvers   = [minBound ..] :: [G.SMTSolver]
sccs      = [minBound ..] :: [G.SCC]
-- minimizes = [minBound ..] :: [G.Minimize]
selectors = [minBound ..] :: [G.Selector]



top = best cmpTimeUB

simple npis = 
  try innermostRuleRemoval
  .>>! top 
    [        npis .>>> empty
    , withDP npis .>>> empty ]
  where
    withDP s = dependencyTuples .>>> try usableRules .>>> try dpsimps .>>! s

px d = poly' (Mixed d) NoRestrict UArgs NoURules 

slogicAll = top     [ px i Nothing       | i <- [1..deg] ]
slogicAny = fastest [ px i (Just selAny) | i <- [1..deg] ]

