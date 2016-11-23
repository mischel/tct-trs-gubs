{-# OPTIONS_GHC -fno-warn-unused-imports #-}
module Main (main) where

import Tct.Core
import Tct.Trs
import Tct.Trs.Interactive

import Tct.Trs.Processor.Poly.GUBS

instance Declared Trs Trs where decls = [ SD gubsDeclaration, SD emptyDeclaration ]

main :: IO ()
main = runTrs trsConfig

