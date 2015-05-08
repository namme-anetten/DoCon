{-# OPTIONS -fno-warn-duplicate-exports #-}
module DExport

  -- All the export of  DoCon + part of GHC exploited by DoCon.
  --
  -- Set the line  import DExport
  -- 
  -- if you are lazy to find more precisely which modules your program
  -- needs 

  (module DPrelude,    module Categs,       module SetGroup,  
   module RingModule,  module Z,            module DPair,  
   module Fraction,    module Permut,       module VecMatr,  
   module Pol,         module Residue,      module LinAlg,  
   module GBasis,      module Partition,    module AlgSymmF,
   module SolveCubic,  module SolveQuartic,

   module Data.Complex, module Data.List, module Data.Ratio, 
   module Prelude, 
   module System.Random    -- non-standard, non-GHC  
                           -- Random.MWC.Pure
  )
where

import System.Random
import Data.Complex
import Data.List hiding (minimum, maximum, sort, sortBy)
import Prelude   hiding (minimum, maximum)
import Data.Ratio 

import DPrelude
import Categs
import SetGroup
import RingModule
import Z
import DPair
import Fraction
import VecMatr
import LinAlg
import Permut
import Pol
import Residue
import GBasis
import Partition
import AlgSymmF
import SolveCubic
import SolveQuartic


