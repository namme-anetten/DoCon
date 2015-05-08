------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
-----------------------------------------------------------------------





module Todiag_  -- Diagonalization of matrix.
                -- LinAlg.hs  reexports necessary items from here.

 (toDiagMatr_euc, test_toDiagMatr_euc)

where
import qualified Data.Map as Map (empty)

import Data.List (transpose)

import SetGroup (Set(..), zeroS, unity       )
import Ring0_   (EuclideanRing(..), upEucRing)

import VecMatr  (Matrix(..), mtHeight, mtWidth, transp, isZeroMt, 
                                                isDiagMt, scalarMt)
import Stairc_  (toStairMatr_euc)





------------------------------------------------------------------------
toDiagMatr_euc ::  
     EuclideanRing a => [[a]] -> [[a]] -> [[a]] -> ([[a]], [[a]], [[a]])
                        -- m     t0       u0        d      t      u

  -- Diagonal form  d  of matrix  m  over a Euclidean ring.
  --
  -- t, u   are the unimodular protocol matrices for the row and the
  --        column transformation respectively.                 
  --
  -- t0 or u0 =  []   is a shorthand for the unity matrix of the
  --                  appropriate size.
  --
  -- Let  h = matrixHeight(m),  wd = matrixWidth(m).
  -- If  t0,u0  are the (h x h) and (wd x wd)  unity  matrices, then  
  --                     t * m * transp(u) = d  
  -- where the (lower) non-zero part of  d is square and diagonal.
  --
  -- This means we first apply the elementary transformation to  the
  -- rows.  If  m  is invertible over  a,  we always achieve the 
  -- diagonal form by this.    If it is not  achieved,  the  similar 
  -- transformations are applied to the *columns*.
  --
  -- Often the returned  u is unity (only row transformations used).
  -- This holds, say, when  m  is *invertible*.
  --
  -- Remark: the determinant can only change sign under the above 
  -- transformations.

toDiagMatr_euc m t u = 
  (case  
       (m, concat $ map concat [m, t, u])
   of
   ([],        es) -> error $ msg es "mM = [].\n"
   ([]: _,     es) -> error $ msg es "mM = ([]: _).\n"
   ((a: _): _, es) -> toD (msg es) (zeroS a) (unity a) (isZeroMt m)
  )
  where
  (hm, wm) = (mtHeight m, mtWidth m)
  msg es   = showString "\ntoDiagMatr_euc mM mT mU,  where mM is\n" . 
             shows hm . showString " x " . shows wm . 
             showString ",\nmM, mT, mU  matrices over the ring  R\n" . 
             msg' es . showChar '\n'
             where 
             msg' []     = id
             msg' (e: _) = showString " =  " . showsDomOf 1 e

  toD _   _  _  True = (m, t, u)
  toD msg zr un _    = 
    let 
      t0 = if null t then  scalarMt m        un zr  else  t 
      u0 = if null u then  scalarMt (head m) un zr  else  u

      (ht, wu) = (mtHeight t0, mtWidth u0)
      msg'     = showString "First row of  mM =  " . shows (head m) . 
                 showString "\n\n"
    in
    case (hm == ht, wm == wu)  
    of
    (False, _    ) -> 
                error $ msg $ msg' $
                showString "height(mM) /= height(mT) = " $ shows ht "\n"
    (_,     False) -> 
                  error $ msg $ msg' $
                  showString "width(mM) /= width(mU) = " $ shows wu "\n"
                               
    _              -> let (s' , t' , _) = toStairMatr_euc ""  m  t0
                          (s'', t'', _) = toStairMatr_euc "u" s' t'
                      in  dm True s'' t'' u0 

  -- Here  s  is a staircase matrix.
  -- If it is not diagonal, then transp(s) it brought to staircase
  -- form - this corresponds to the column elementary 
  -- transformations of s -  and so on,  until the diagonal matrix 
  -- is obtained (even number of `transp' to be applied).

  dm even s t u = 
     case (even, isDiagMt s, transpose s) 
     of
     (True , True , _ ) -> (s , t, u)
     (False, True , s') -> (s', t, u)
     (True,  False, s') -> dm False s'' t u'  
                                  where
                                  (s'', u', _) = toStairMatr_euc "" s' u
     (False, False, s') -> dm True s'' t' u
                                  where
                                  (s'', t', _) = toStairMatr_euc "" s' t
                               

------------------------------------------------------------------------
test_toDiagMatr_euc :: EuclideanRing a => [[a]] -> String
test_toDiagMatr_euc m =  
  case m 
  of
  []        -> error "\ntest_toDiagMatr_euc [].\n"
  []: _     -> error "\ntest_toDiagMatr_euc ([]: _).\n"
  (a: _): _ -> "\nDiagonal form  d =\n\n" ++ (d_str ++ eq_str)
               where
               dom              = upEucRing a Map.empty
               (d, t, u)        = toDiagMatr_euc m [] []
               [m', d', t', u'] = [Mt x dom | x <- [m, d, t, u]]
               m_by_tu = t'*m'*(transp u')
               d_str   = shows d' ""
               eq_str  = if m_by_tu == d' then  
                                     "\n\n  t*m*transp(u) = d   O.K.\n"
                         else        "\n\nERROR:  t*m*transp(u) /= d.\n"
