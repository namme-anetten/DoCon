----------------------------------------------------------------------
----------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2011
----------------------------------------------------------------------
----------------------------------------------------------------------




-- Demonstration, test, benchmark.
-- Diagonalization of matrix over K[x],  K a finite field.
-- M -> T*M*U = Diagonal, 
-- T, U made of elementary transformations on rows and columns
-- respectively.

module T_diagmatr (t_diagmatr_)
where
import qualified Data.Map as Map (empty)

import DPrelude   (smParse, ctr, mapmap)
import Categs     (PIRChinIdeal(..), ResidueE(..))
import RingModule (eucIdeal, upEucRing, upField  )
import Z          (dZ)
import VecMatr    (Matrix(..), transp)
import Pol        (UPol(..), cToUPol)
import LinAlg     (det, toDiagMatr_euc)


type R = Integer
type K = ResidueE R   -- K = R/(p)
type P = UPol K 

t_diagmatr_ =  
  ([pr == mD', detD == detM || detD == (-detM)], (mM', mD', detM, detD))
  where
  (dR, p) = (dZ, 3 :: R)
  iI      = eucIdeal "bef" p [] [] []   :: PIRChinIdeal R
  r0      = Rse 0 iI dR                           -- 0 of K
  [r1, r2, r3, r4] = map (ctr r0) [1 .. (4 :: R)] 
                                  -- short denotation for residues,
                                  -- here ctr projects things to residue
  dK  = upField r0 Map.empty               -- description for K = R/iI
  unp = cToUPol "x" dK r1  :: P
  dP  = upEucRing unp Map.empty            -- description for P = K[x]
  mM  = mapmap (smParse unp) [["2*x+1", "(x+2)^2+1",  "0"],
                              ["x",     "0",          "x"],
                              ["x^2",   "2",          "1"]]  :: [[P]]
  detM         = det mM    
  (mD, mT, mU) = toDiagMatr_euc mM [] []

  [mM', mD', mT', mU'] = [Mt m dP | m <- [mM, mD, mT, mU]]
  detD = det mD                  -- has to be +- detM
  pr   = mT'*mM'*(transp mU')    -- has to be  mD'

{-  ("M     = \n"++)$ shows mM' $    ("\n\n"++)$
    ("D     = \n"++)$ shows mD' $    ("\n\n"++)$
    ("detM  = \n"++)$ shows detM $   ('\n':)$
    ("detD  =   "++)$ shows detD $   ("\n\n"++)$
    ("pr==D =   "++)$ show (pr==mD') 
-}
