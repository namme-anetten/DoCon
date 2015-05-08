------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge D.Mechveliani,  2012
------------------------------------------------------------------------
------------------------------------------------------------------------




module SymmFn0_  -- Continuation for  SymmFn_.
                 -- All needed from here is reexported by  AlgSymmF.

(sToH_, sToE_, sToP_, sToM_, mToP_, shifts_)
where
import qualified Data.Map as Map 
                      (empty, lookup, findWithDefault, insert, fromList)

import Data.Maybe (fromMaybe)

import DPrelude (ct, factorial, allMaybes, showsWithDom, 
                                           addListToMapWith)
import Categs     (Dom(..)                              )
import SetGroup   (MulSemigroup(..), zeroS, times, unity)
import RingModule (CommutativeRing(), Field()           )
import UPol_      (PolLike(..), cPMul                   )
import LinAlg     (inverseMatr_euc                      )
import Partition  (Partition, prttWeight, pLexComp, conjPrtt, 
                   prttLength, prttUnion, prttsOfW, kostkaTMinor,
                   permGroupCharTMinor
                  )
import Sympol_ (SymPol(..), symPolMons, reordSymPol, symLdPrtt, 
                                                       symPolHomogForms)
import SymmFn_ (SymFTransTab, transpPtP, h'to_p_coef, intListToSymPol)
import qualified SymmFn_ (msgDcSum_, msgPtLkpK_)
           




------------------------------------------------------------------------
sToH_, sToE_, sToP_, sToM_ ::
                              -- transformations from 's' to other bases
  CommutativeRing a =>
                    SymFTransTab -> SymPol a -> (SymFTransTab, SymPol a)
                    -- tab          f            tab'          h

------------------------------------------------------------------------
sToH_ tab f =  foldl decompAndSum (tab, zeroSP) $ symPolHomogForms f'
 where
 -- METHOD:  M(s,h) = inv(tK) the inverse transposed Kostka matrix.
 -- For each  w  tK(w)  is found in  tab  (or initiated by  empty), 
 -- completed with some rows from (kostkaTMinor..)  and inverted.
 -- New tK is stored.  It is used that inv(tK) is lower triangular.

 f'     = reordSymPol pLexComp f
 zeroSP = zeroS f'
 msg    = showString "\nSymmetric bases transformation  sToH_ table f" . 
          showsWithDom 1 f "f" ""
                             
 decompAndSum (tab, res) f =          -- here f is homogeneous, non-zero
     
              (if w == 0 then (tab, res + f)             -- case deg = 0
               else           (Map.insert w (allPts, tC, tK) tab, res')) 
   where
   w                 = prttWeight $ symLdPrtt f
   (allPts, tC, tK') = Map.findWithDefault
                         (prttsOfW [(w, 1)], Map.empty, Map.empty) w tab 

   forcedPRows = zip allPts $ kostkaTMinor allPts allPts
                                              -- columns who's p are not
                                              -- in tK' will evaluate 
   tK  = addListToMapWith (\ old _ -> old) tK' forcedPRows      
   itK = case allMaybes [Map.lookup p tK | p <- allPts]  
         of
         Just tKRows -> 
                      Map.fromList $ zip allPts $ inverseMatr_euc tKRows
         _           ->
             error $ msg $ SymmFn_.msgDcSum_ f "fh"
                    "Kostka matrix tK (from table) wrongly completed.\n"

                              -- convert SymMon to sym-polynomial in "h"
   convMon (c, la) = 
              case  Map.lookup la itK  
              of
              Just row -> cPMul c $ intListToSymPol 'u' f' la allPts row
              _        -> error $ msg $ SymmFn_.msgDcSum_ f "fh" $ 
                                        SymmFn_.msgPtLkpK_ la "itK" "\n"
   res' = foldl (+) res $ map convMon $ symPolMons f


msgDivFChar fName =                                  
      showString 
      (concat ["Division failed in the coefficient domain K.\n\
               \Mind also that  ", fName,
               "  requires  K  to be a Field of zero characteristic\n"])


------------------------------------------------------------------------
sToE_ tab f =  foldl decompAndSum (tab, zeroSP) $ symPolHomogForms f'
 where
 -- METHOD:  m(s,e) =  J*inv(tK).
 -- So it is like  sToH_, only for each  s(la)  it is found the row of 
 -- la' (instead of la)  in  inv(tK). 

 f'     = reordSymPol pLexComp f
 zeroSP = zeroS f'
 msg    = showString "\nSymmetric bases transformation  sToE_ table f" . 
          showsWithDom 1 f "f" ""

 decompAndSum (tab, res) f =          -- here f is homogeneous, non-zero  

              (if w == 0 then (tab, res + f)             -- case deg = 0
               else           (Map.insert w (allPts, tC, tK) tab, res')) 
   where
   w                 = prttWeight $ symLdPrtt f
   (allPts, tC, tK') = Map.findWithDefault
                       (prttsOfW [(w, 1)], Map.empty, Map.empty) w tab 

   forcedPRows = zip allPts $ kostkaTMinor allPts allPts
                                                 -- rows who's p are not
                                                 -- in tK' will evaluate
   tK = addListToMapWith (\ old _ -> old) tK' forcedPRows      
   itK = case  allMaybes [Map.lookup p tK | p <- allPts]  
         of
         Just tKRows -> 
                      Map.fromList $ zip allPts $ inverseMatr_euc tKRows
         _           -> 
                  error $ msg $ SymmFn_.msgDcSum_ f "fh" 
                    "Kostka matrix tK (from table) wrongly completed.\n"

   convMon (c, la) =          -- convert SymMon to sym-polynomial in "e"
             let la' = conjPrtt la
             in
             case Map.lookup la' itK  
             of
             Just row -> cPMul c $ intListToSymPol 'u' f' la' allPts row
             _        -> error $ msg $ SymmFn_.msgDcSum_  f "fh" $ 
                                      SymmFn_.msgPtLkpK_ la' "itK" "\n"

   res' = foldl (+) res $ map convMon $ symPolMons f


------------------------------------------------------------------------
sToP_ tab f =  foldl decompAndSum (tab, zeroSP) $ symPolHomogForms f'
 where
 -- METHOD:   M(s,p) = inv(tC)   
 --           inverse to the irreducible character matrix.
 -- The rows of  tC  are mutually orthogonal. So   tC*C = D  
 -- for some diagonal matrix D. 
 -- Hence                       M(s,p) = C*inv(D) = t(tC)*inv(D).
 -- This means to divide each column of t(tC)  by corresponding diagonal
 -- elements  zs  of  D.
 -- zs  are the integer coefficients of the factorial nature. 
 --     They are called  z(la) in [Ma], la the partition - see 
 --     h'to_p_coef.   
 -- The above division by z(la) is performed after converting of each 
 -- monomial of  f(w),  that is after  intListToSymPol.
 -- 
 -- For each w,  tC  is obtained by completing of the matrix tC' 
 -- extracted from  tab.  And tC' = empty,  if lookup fails.
 -- Completing means adding some rows of  (permGroupCharTMinor..).
 -- And naturally, tC is stored instead of tC'.

 (f', un)     = (reordSymPol pLexComp f, unity $ sample f)
 zeroSP       = zeroS f'
 divBy_zs f   = ct f $ map divZ $ symPolMons f
 divZ (a, pt) = let hpc = times un $ h'to_p_coef pt
                in
                case divide_m a hpc  
                of
                Just b -> (b, pt)
                _      -> error $ msg $ msgDivFChar "sToP_" ""

 msg = showString "\nSymmetric bases transformation  sToH_ table f" . 
       showsWithDom 1 f "f" ""
 -----------------------------------------------------------------------
 decompAndSum (tab, res) f =          -- here f is homogeneous, non-zero 

              (if w == 0 then (tab, res + f)            -- case deg = 0
               else           (Map.insert w (allPts, tC, tK) tab, res'))
   where
   w                 = prttWeight $ symLdPrtt f
   (allPts, tC', tK) = Map.findWithDefault
                         (prttsOfW [(w, 1)], Map.empty, Map.empty) w tab

   forcedPRows = zip allPts $ permGroupCharTMinor allPts allPts
                                                 -- rows who's p are not
                                                 -- in tC' will evaluate 
   tC = addListToMapWith (\ old _ -> old) tC' forcedPRows      
   mC = transpPtP tC
                          -- convert SymMon to sym-polynomial in "p"
                          -- according mC and the divisors  z(mu)
   convMon (c, la) = divBy_zs g
               where
               row = fromMaybe (error $ msg $ SymmFn_.msgDcSum_ f "fh" $
                                showString "Row of  " $ shows la 
                                 "\nnot found in the built  M(s,p).\n"
                               ) $
                               Map.lookup la mC
               g = cPMul c $ intListToSymPol 'a' f' [] allPts row

   res' = foldl (+) res $ map convMon $ symPolMons f


------------------------------------------------------------------------
sToM_ tab f =  foldl decompAndSum (tab, zeroSP) $ symPolHomogForms f'
 where
 -- METHOD:  M(m,s) = K  the Kostka matrix,
 --                     tK from tab being completed and transposed.

 f'     = reordSymPol pLexComp f
 zeroSP = zeroS f'
 msg    = showString "\nSymmetric bases transformation  sToM_ table f" . 
          showsWithDom 1 f "f" ""

 decompAndSum (tab, res) f =          -- here f is homogeneous, non-zero 

              (if w == 0 then (tab, res + f)            -- case deg = 0
               else           (Map.insert w (allPts, tC, tK) tab, res'))
   where
   w                 = prttWeight $ symLdPrtt f
   (allPts, tC, tK') = Map.findWithDefault
                         (prttsOfW [(w, 1)], Map.empty, Map.empty) w tab 

   forcedPRows = zip allPts $ kostkaTMinor allPts allPts
   tK = addListToMapWith (\ old _ -> old) tK' forcedPRows
   mK = transpPtP tK
   convMon (c, la) =    -- convert sym-monomial to sym-polynomial in "m"
              case Map.lookup la mK  
              of
              Just row -> cPMul c $ intListToSymPol 'l' f' la allPts row
              _        -> error $ msg $ SymmFn_.msgDcSum_ f "fh" $ 
                                        SymmFn_.msgPtLkpK_ la "mK" "\n"

   res' = foldl (+) res $ map convMon $ symPolMons f



------------------------------------------------------------------------
mToP_ :: Field k => SymPol k -> SymPol k
                    -- f        h
{-              
Example:  m[1^2] = e(2)  -->  (1/2)*p[1]^2 - (1/2)*p[2]
METHOD.
The below NS method had occurred considerably cheaper in forming the
whole matrix  M(p,m)  then the method based on the inverse Kostka 
matrix and the inverse irreducible character  matrix  C  - even when 
the latter uses the orthogonality of C.

It is taken from the ancient book of  I.Serret  on higher algebra,
and we call it here the Newton-Serret formula.  It is a slight
generalization of the Newton formula and of the evident equality

  m[i]*m[j,k] =  m[i,j,k] + m[j+i,k] + m[j,k+i]   for i > j > k.

For the expanded diagrams, this decomposition `o' is as follows:

  o(i:js) =  ( c(js)*pi*o(js) - sum ) / c(i:js)
    where
    sum = sum [ c(js')*o(js') |  js'= js+i*e(t),  t<-[1..|js|] ],

    e(t)   the unity vector of t-s coordinate,
    c(ks)  the coefficient factor, the factorial of the length of 
           each group of equal coordinates in  ks.

The real algorithm uses the list-of-integer-pairs representation of
a diagram (see SymPol.hs). 
The function `shifts' for diagr+k*e(i) gathers the equivalent result
diagrams into one pair with the integer multiplicity:  (i,diagr').  
And it uses that all the shifts of  [j,j..j]<->(j,m)
equal to the same partition.  Also the shifting takes in account 
that the result diagram is ordered as it must be, say, 
[j,j+k] -> [j+k,j].
So  mToP_  

1. Takes (a,pt) = head-sym-monomial(f);  (k,m) = head pt;
   restDiag = restDiagram pt,
   the one corresponding to the expanded diagram without first k.
2. Forms the linear combination of the shifted diagrams
   restDiag + k*e(t)  according to the above `o' formula and 
   subtracts this combination from the tail of f by subtracting of
   the sym-polynomials, (the diagram lists merge in lex order); 
   each of the new-coming diagrams is shorter than pt; 
   f_new  is formed.
3. monConverted =  p(k) * o(restDiag) * certainCoefficient,
   where
   o(restDiag) = restMonConverted   computes by applying  mToP_
   to the monomial sym-polynomial with the shorter diagram,
   (p(k) *)  means to union each diagram in restMonConverted with
   the diagram [(k,1)].
4. The result is  monConverted + mToP_(f_new)

Optimization:
m[1^n] = e(n)  is converted specially, according to the explicit 
formula
  e(n)        = sum( (epsilon(la)/z(la))*p(la) |  |la| = n ),
  epsilon(la) = (-1)^(|la| - l(la)),
  z( [(i1,m1)..(il,ml)] ) = product( (i(k)^m(k))*m(k)! | k <- [1..l])
-}

mToP_ f = mToP $ symPolMons f'
  where
  (f', un) = (reordSymPol pLexComp f, unity $ sample f)
  zeroSP   = zeroS f'
  msg      = showString "\nSymmetric bases transformation  mToP_ f" . 
             showsWithDom 1 f "f" ""

  mToP []                      = zeroSP
  mToP [(a, [])]               = ct f' a 
  mToP ((a, (k, m): q): monsT) = 
    case (k, m, q) 
    of
    (1, _, _ ) -> cPMul a (em_to_p m)                 -- f = a*e(m)
    (_, 1, []) -> let p = [(k, 1)] :: Partition       --     a*p(k)+tail
                  in  (ct f' (a, p)) + (mToP monsT) 
    _          -> monConverted + (mToP newMons)
      where
      restDiag     = if m == 1 then  q  else  (k, pred m): q
      cRestI       = cFactor restDiag
      cRest        = times un cRestI    
      totalDivisor = times un (m*cRestI)
      (ints, shiftsOfRest) = unzip $ shifts_ k restDiag
                        -- `shifts' yields the multiplicities which have
                        -- also to multiply by their  cFactor-s
                   
      cs = zipWith mulDiv ints $ map cFactor shiftsOfRest
                        where
                        mulDiv j k = (a*(times un (j*k))) / totalDivisor
 
      shiftsPol        = ct f' $ zip cs shiftsOfRest
      newMons          = symPolMons ((ct f' monsT) - shiftsPol)
      restMonConverted = mToP [(a*cRest, restDiag)]

      ms = case pCDiv restMonConverted totalDivisor 
           of
           Just g -> symPolMons g
           _      -> error $ msg $ msgDivFChar "mToP_" ""

      msBy_pk = [(c, prttUnion [(k, 1)] q) | (c, q) <- ms]
                                          -- form p(k)*convertedMonomial
      monConverted = ct f' msBy_pk 
  ----------------------------------------------------------------------
  em_to_p m =      -- e(m) = sum( (epsilon(la)/z(la))*p(la) | |la| = m )
              ct f' [(coef la, la) | la <- pts]
    where
    pts        = prttsOfW [(m, 1)]
    epsilon la = even ((prttWeight la) - (prttLength la))
    coef la    =  
             let b = times un $ h'to_p_coef la
             in
             case (epsilon la, divide_m un b)
             of
             (True, Just q) ->  q
             (_,    Just q) -> -q
             _              -> 
                error $ msg $ showString "It calls   em_to_p " $ 
                   shows m $ showString "\n:\n" $ msgDivFChar "mToP_" ""

                       -- factorial-nature factor for the Young diagram
  cFactor []    = 1 
  cFactor pairs = product $ map (factorial . snd) $ pairs


------------------------------------------------------------------------
shifts_ :: Integer -> Partition -> [(Integer, Partition)]

-- LOCAL thing. 
-- Auxiliary for  m_to_p, m_to_e_via_p_pol  in this module.
-- Let                  shifts' k js --> [js+k*e(t), t<-[1..|js|]]
-- for the integer list  js,  k > js.
-- shifts_  k  diag@[(j1, m1) .. (jl, ml)] --> 
--                                  [(i(1), diag(1)) .. (i(u), diag(u))]
-- acts similar on the true partition.
-- And it must preserve the lex order.

shifts_ _ []              = []
shifts_ k ((j, m): pairs) =  
              let pairs'               = map insert_jm (shifts_ k pairs)
                  insert_jm (i, p: ps) = ( i, p: (j, m): ps )
                  prepRest_j = if m == 1 then  id  else  ((j, pred m) :)
              in
              (m, (k+j, 1): (prepRest_j pairs)) : pairs'
