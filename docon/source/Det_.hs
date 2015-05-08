------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------





module Det_                   -- Determinant of matrix.
                              -- LinAlg  reexports all needed from here.
(det, det_euc, maxMinor, delColumn, adjointMt) 
where
import Data.List (transpose)

import DPrelude (Length(..), -- class
                 Natural,  sortE, product1, del_n_th, invSign, compBy, 
                                                   showsn, showsWithDom)
import SetGroup (zeroS, neg)
import Ring0_   (CommutativeRing(), EuclideanRing(..))
import VecMatr  (mainMtDiag, mtHeight, mtWidth, isZeroMt, isStaircaseMt)
import Stairc_  (toStairMatr_euc)




------------------------------------------------------------------------
delColumn :: Natural -> [[a]] -> [[a]]
delColumn i =  map (\ xs -> del_n_th i xs)

maxMinor :: Natural -> Natural -> [[a]] -> [[a]] 
                                      -- pre-matrix obtained by deleting
                                      -- of  i-th row  and  j-th column  
maxMinor i j rows = delColumn j $ del_n_th i rows

------------------------------------------------------------------------
det :: CommutativeRing a => [[a]] -> a

-- Determinant of square  matrix.
-- ATTENTION: 
-- it simply  expands det(M) by the row  
-- (after moving ahead the rows which contain more of zeroes).  
-- It has the maximal cost of  O(n!).
--
-- For the  Euclidean case,  it is also provided  det_euc 
-- of the Gauss method.

det []            = error "\ndet [].\n"
det ([]: _)       = error "\ndet ([]: _).\n"
det m@((a: _): _) =  
  let  
    (zr, n, width) = (zeroS a, mtHeight m, mtWidth m)
    expandByRow [[a]]       = a
    expandByRow (row: rows) = dt 1 '+' row rows zr
                                        -- initiate det = zr, sign= '+',
                                        -- for i=1 to n ...
    dt _ _     []      _    res = res 
    dt i sign  (a:row) rows res = 
      if  
        a == zr  then  dt (succ i) (invSign sign) row rows res  
                                                            -- skip zero
      else
      let minorDet = expandByRow $ delColumn i rows
      in
      case sign of '+' -> dt (i+1) '-' row rows (res + a*minorDet)
                   '-' -> dt (i+1) '+' row rows (res - a*minorDet)
    --------------------------------------------------------------------
  in 
  if  n < 1 || n /= width  then
      error $ concat ["\ndet mM,", showsWithDom 1 a "mtHead mM" ""
                                 "\nmM must be non-empty and square.\n"]
  else
  let addNum row = (row, genLength $ filter (== zr) row)
      pairs              = map addNum m
      (sortedPairs,sign) = sortE (flip (compBy snd)) pairs
      dt                 = expandByRow $ map fst sortedPairs
  in
  if sign == '+' then dt else (- dt)


-----------------------------------------------------------------------
det_euc :: EuclideanRing a => [[a]] -> a

-- Determinant of square matrix over a Euclidean ring
-- computed via the Gauss reduction to the staircase form.
-- For the field case, its maximal cost is  O(n^3)  of division 
-- operations.

det_euc []            = error "\ndet_euc [].\n"
det_euc ([]: _)       = error "\ndet_euc ([]: _).\n"
det_euc m@((a: _): _) = 
  case (zeroS a, mtHeight m, mtWidth m)  
  of
  (zr, n, width) ->
    if 
      n < 1 || n /= width  then  
      error $ concat ["\ndet_euc mM,", showsWithDom 1 a 
                "mtHead mM" "" "\nmM must be non-empty and square.\n"]
    else
    if isZeroMt m then  zr
    else
    if isStaircaseMt m then  product1 $ mainMtDiag m
    else
    let (s, _, sign) = toStairMatr_euc "" m []
        dt           = product1 $ mainMtDiag s
    in  if sign=='+' then  dt  else (- dt)


------------------------------------------------------------------------
adjointMt :: CommutativeRing a => [[a]] -> [[a]]
                                           -- mM
-- = A = adjoint matrix of mM.  A(i,j) = coMinorDet(j,i),
-- where  coMinorDet(k,l) is the cofactor in the inverse matrix formula.
-- For a square matrix mM, it holds  
--                            mM*(adjointMt mM) == (det mM)*UnityMatrix.

adjointMt mM = if  mtHeight mM == mtWidth mM  then
                                 transpose $ reverse $ adm True [] mM []
               else 
               error ("\nadjointMt\n" ++ 
                      (showsn 1 mM "\n:\na square matrix expected.\n"))
 where
 minusIf ev = if ev then id else neg

 adm :: CommutativeRing a => Bool -> [[a]] -> [[a]] -> [[a]] -> [[a]]
 adm                        evenness usedRows remRows  resRows = 
        case remRows 
        of
        []            -> resRows
        row: remRows' -> adm (not evenness) (usedRows ++ [row]) remRows' 
                             ((cpRow evenness 1 row): resRows)
             where
             cpRow _  _ []       = []
             cpRow ev j (_: row) = (minusIf ev $ det $ complemMinor j) :
                                   (cpRow (not ev) (succ j) row)
                     where
                     complemMinor j = delColumn j (usedRows ++ remRows')
