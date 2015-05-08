------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------






module LinAlg     -- Linear Algebra.  The head module.

(diagMatrKernel, solveLinear_euc, solveLinearTriangular, 
 test_solveLinear_euc,

 -- from Stairc_:
 reduceVec_euc, toStairMatr_euc, rank_euc, inverseMatr_euc,     
 linBasInList_euc, test_toStairMatr_euc, test_inverseMatr_euc,

 det, det_euc, maxMinor, delColumn, adjointMt,           -- from Det_
 toDiagMatr_euc, test_toDiagMatr_euc                     -- from Todiag_
)
where

import qualified Data.Map as Map (empty, lookup)

import Data.List (transpose, genericDrop, genericSplitAt, 
                                                       genericReplicate)

import DPrelude (Length(..), -- class 
                 PropValue(..),  takeAsMuch, dropAsMuch, showsn, 
                                                         showsWithDom)
import Categs   (CategoryName(..), Domain1(..))
import SetGroup (MulSemigroup(..), zeroS, unity)
import Ring0_   (Ring(..), CommutativeRing(..), EuclideanRing(..), 
                 isField, upEucRing)
import VecMatr 
import Stairc_ 
import Det_   
import Todiag_  





------------------------------------------------------------------------
diagMatrKernel :: Ring a => [[a]] -> [[a]]

-- Kernel basis  ker  for a  diagonal matrix  D  having NO zero rows on 
-- diagonal
-- (hence, height(D) <= width(D),  D*(transpose ker) = zeroMatrix))
--
-- The domain must be a  ring with unity and No zero divisors.
-- The result is  []  for the zero kernel.

diagMatrKernel  []             = error "\ndiagMatrKernel [].\n"
diagMatrKernel  ([]: _)        = error "\ndiagMatrKernel ([]: _).\n"
diagMatrKernel  mD@((a: _): _) =     
  let
    (z, u, h) = (zeroS a, unity a, mtHeight mD)
    hZeroes   = map (const z) mD
  in
  case genericDrop h $ head mD  
  of
  []      -> []
  rowRest -> map (hZeroes ++) $ scalarMt rowRest u z   -- unity matrix

------------------------------------------------------------------------
solveLinear_euc :: EuclideanRing a => [[a]] -> [a] -> ([a], [[a]])
                                      -- mM    v       p    ker
-- General solution  of the linear system: 
--                                 mM * (transp [x]) == (transp [v])
--
-- mM  is  n x m  matrix,   v  is the vector of size  n.
-- p    is the row for some partial solution,
--      it is  []  if there is no such solution.
-- ker  is the rows generating the  `a'-module of solutions  for 
--      the homogeneous system          mM * transp(x) = zeroColumn.
--      ker = []  if the kernel is {0}.
-- METHOD.
-- m  converts to the diagonal form by  Gaussian elimination  for the
-- rows and columns (the remainder division repeating); the
-- corresponding transformation matrices  t, u  are accumulated.
-- Then the diagonal system is solved, and the goal solution is
-- restored using  t, u.
-- IsField  is tested for `a' to separate the easy case.
        
solveLinear_euc _   []      = error "\nsolveLinear_euc _ [].\n"
solveLinear_euc mM  v@(a:_) =
  let  
    (n, mA)       = (mtHeight mM, transpose [v])
    (zr, un, dom) = (zeroS a, unity a, upEucRing a Map.empty)

    fld = case Map.lookup Ring dom   
          of  
          Just (D1Ring aR) -> isField aR
          _                ->
                            error $ msg "\nRing term not found in  R.\n"
    msg = showString "solveLinear_euc mM v," . 
          showsWithDom 1 a "head v" "R"
    --------------------------------------------------------------------
    solve mM mA =               -- Main part. Starts after initial check
      let
        (row, mA_isZero) = (head mM, isZeroMt mA)
        zeroRow          = map (const zr) row
      in
      if isZeroMt mM then let unMatr = scalarMt row un zr
                              p      = if mA_isZero then zeroRow else []
                          in  (p, unMatr)
      else
      if  fld == Yes && mA_isZero  then (zeroRow, ker_field mM)
                                                -- special "cheap" case
      else  
      let (mS', mA', _) = toStairMatr_euc "" mM mA
                                    -- reducing the system, start with
                                    -- t0 = mA  rather than unity matrix
          (s'', _ )    = span (any (/= zr)) mS' 
          h''          = mtHeight s''
          (a'', a''tl) = genericSplitAt h'' mA'
                                           -- partial solution fails
                                           -- if  a''tl  is not all zero
          (mD, mT, mU) = toDiagMatr_euc s'' [] []
                                   -- mD is diagonal, free of zero rows,
                                   -- and   mT*s''*transp(mU) = mD
          kD = diagMatrKernel mD 
          [mA'', mmT, mmU, mkD] = [Mt x dom | x <- [a'', mT, mU, kD]]
          ker  = if  null kD  then []  else  mtRows (mkD*mmU)
          ptsD = pSolDiag mD (mtRows (mmT*mA'')) h''
      in
      if  all (== [zr]) a''tl  &&  genLength ptsD == mtHeight mU 
      then  (rowMatrMul ptsD mU, ker) 
      else  ([],                 ker)
    --------------------------------------------------------------------
    -- The list  pts  for the partial solution of a diagonal 
    -- matrix  mD  having No zero rows (hence  height <= width).     
    -- pts = []  if there is no solution.

    pSolDiag mD rows n = ps (mainMtDiag mD) rows
        where
        ps []      []          = genericReplicate ((mtWidth mD) - n) zr
        ps (d: ds) ([a]: rows) = case divide_m a d of
                                              Nothing -> []
                                              Just q  -> q: (ps ds rows)
        ps _      _             = 
                error $ msg $ showString "\n... pSolDiag mD rows " $ 
                              shows n "\n\nWrong arguments  mD, rows \n"
    --------------------------------------------------------------------
    -- Kernel basis  for the field case.
    -- The simplest version of the Gauss method.

    ker_field rows = filter (any (/= zr)) $ ker rows
      where
      ker (row: rows) =
        let
          rowT    = tail row
          zeroesT = map (const zr) rowT
          unRs    = scalarMt rowT un zr   -- unity (m-1)x(m-1)
        in
        case span ((== zr) . head) (row:rows)
        of
        (_,    []          ) ->                           -- zero column
                if  null rowT then [[un]]
                else 
                (un: zeroesT): (map (zr :) $ ker (rowT:(map tail rows)))

        (z1rs, (a: row): rs) ->  
            if  
              null rowT then [(zr: zeroesT)]
            else
            let  
              reduceRow (b: row') =  
                           if  b == zr  then  b:row'
                           else 
                           zr: (zipWith (\ x y -> x - (b/a)*y) row' row)

              rs' = z1rs ++ (map reduceRow rs)       
                                            -- rs' has size (n-1) x m
                                            -- and has zero first column

                    -- M = (a:row):rs' -T-> M'= [[a]]+(map tail rs')
                    -- reduces the task to the solution for the 
                    -- direct sum of matrices, T corresponds to the
                    -- transformation  y1 = x1, yi = xi+ci*x1,  
                    -- ci = -a1i/a,  i = 2..n.

              us    = if null rs' then unRs  else  ker $ map tail rs'
              kerM' = map (zr :) us  
              csv   = un: [-b/a | b <- row] 
              heads = map (scalProduct csv) kerM'
            in
            zipWith (:) heads $ map tail kerM'
    --------------------------------------------------------------------
  in 
  if  (n /= mtHeight mA) || n < 1  then
      error $ msg 
              "\nNon-empty mM  required and  mtHeight(mM) = size(v)\n"
  else        solve mM mA



------------------------------------------------------------------------
test_solveLinear_euc :: EuclideanRing a => [[a]] -> [a] -> String

test_solveLinear_euc  _   []      =  
                                  error "\ntest_solveLinear_euc _ [].\n"
test_solveLinear_euc  mM  v@(a:_) =  

  concat [p_s, ker_s, productEqA_s, imageIs0_s, dimKer_s]
  where
  aD              = upEucRing a Map.empty
  dimKerNeeded mt = (mtWidth mt) - (rank_euc mt)
  mA              = transpose [v]
  (p, ker)        = solveLinear_euc mM v

  p_s = if null p then "\nno partial solution \n\n"
        else         "\npartial solution  P = \n" ++ (showsn 1 p "\n\n")

  [mM', mA', mP', ker'] = [Mt x aD | x <- [mM, mA, [p], ker]]

  ker_s        = "\n\nkernel  ker = \n" ++ (showsn 1 ker' "\n\n")
  productEqA_s =
        if null p then ""
        else
        if  mM'*(transp mP') == mA'  then  
                                     "M*transp(P) = transp [v]  OK \n\n"
        else  "ERROR:  M*transp(P) /= transp [v].\n"
              ++ "Is the ring Euclidean?\n\n"     

  imageIs0_s = 
      if  null ker then  "M*transp(Ker) = 0  OK\n\n"
      else
      if  isZeroMt $ mtRows (mM'*(transp ker'))  then  
                                             "M*transp(Ker) = 0  OK\n\n"
      else  "ERROR.  solveLinear_euc:  M*transp(Ker) /= 0.\n\n"

  dimKer   = if null ker then 0 else rank_euc ker 
  dimKer_s = if  dimKer == dimKerNeeded mM  then  "dim(Ker)  is OK\n\n"
             else         "ERROR. solveLinear_euc:  wrong dim(Ker)\n\n"


------------------------------------------------------------------------
solveLinearTriangular :: CommutativeRing a => [[a]] -> [a] -> Maybe [a] 
                                              -- mA    row    

-- Solving a system                     xRow x mA' = row      (1)
-- for an upper-triangular matrix  mA'.
-- Size agreement:
--   mA  is restricted to the main minor  mA'  of size  |row| x |row|,
--   the remaining part is removed, the solution is for  mA'. 
-- Hence  |xRow| = size mA' = |row|.
-- 
-- If `a' is free of zero divisors,  mA' is upper triangular and has 
-- not zeroes on the main diagonal, then this function satisfies the 
-- property:
--   if (1) has solution then solveLinearTriangular returns  Just xs,
--                                   where xs is this (unique) solution,
--   otherwise it returns  Nothing.
--
-- Method
-- ------  
-- The usual method for solving a triangular system:  
-- find x(1), then find x(2) via x(1), and so on. 
-- Cost =  O (|row|^2).

solveLinearTriangular mA row = 

  if  null row  then  error $ messg "empty right-hand side.\n"
  else
  if  null mA  then  error $ messg "empty matrix.\n"
  else               fmap (++ zeroes) $ solve [] (transpose cutA) nzRow

  where
  zr              = zeroS $ head row
  (zeroes, nzRow) = span (== zr) row
  cutA            = map (dropAsMuch zeroes) $ dropAsMuch zeroes $ 
                    map (takeAsMuch row) mA

  solve xs columns row =  
    case (columns, row) 
    of 
    ([],         _      ) -> Just xs
    (col: cols', b: row') -> 
      (case  
           divide_m b' a  of  Nothing -> Nothing 
                              Just x  -> solve (xs ++ [x]) cols' row'
      )
      where
      colUp = takeAsMuch (b: xs) col    -- part of  col  [top..diagonal]
      a     = last colUp
      b'    = b - (scalProduct xs col)
                      -- express x from  (scalProducct xs col) + x*a = b

  messg = showString "\nsolveLinearTriangular mA\n " . shows row . 
          showString "\n:\n"