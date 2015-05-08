------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge D. Mechveliani,  2012
------------------------------------------------------------------------
------------------------------------------------------------------------




module SymmFn1_      -- Continuation for SymmFn0_.
                     -- All needed from here is reexported by  AlgSymmF.

(powerSumsTo_e, mToEViaP_pol_)
where
import qualified Data.Map as Map (empty)

import Data.List (genericIndex)

import DPrelude (Length(..), -- class 
                 ct, ctr, factorial, sum1, alteredSum, showsn, 
                                                       showsWithDom)
import Categs     (Dom(..))
import SetGroup   (zeroS, times, unity)
import RingModule (CommutativeRing(), upField)
import Fraction   (Fraction(..), num, denom, zeroFr)
import Pol        (PolLike(..), Pol(..), deg0, lexPPO, polMons, cPMul, 
                                                                cToPol)
import Partition (pLexComp)
import Sympol_   (SymPol(..), symPolMons,reordSymPol, cToSymPol)
import SymmFn0_  (shifts_)


           


------------------------------------------------------------------------
powerSumsTo_e :: CommutativeRing a => Pol a -> [Pol a]
                                      -- f     [e(1)..e(n)]
-- Expressions of h-power sums  p(i),  i <- [1..n]  
-- as polynomials of elementary symmetrics  e(i) <- R[e1'..en'].
--
-- f  is a  sample polynomial for  R[e1'..en'].
-- n  = number of variables in f.
-- METHOD.
-- Newton formula:  p(k) = e1*p(k-1) - e2*p(k-2) +...+ ((-1)^(k+1))*k*ek

powerSumsTo_e f = upto_n 2 [head sPols]
  where
  sPols           = varPs un f
  (vars, unP, un) = (pVars f, unity f, unity $ sample f) 
  n               = genLength vars   -- <-> [e1..en]

  upto_n k es = if k > n then  es            -- 2 [e(1)] -> [e(1)..e(n)]
                else
                let ps = reverse ((times unP k): es) 
                                          -- zip [e(k-1).. e(1),   k   ]
                                          --     [s(1)  .. s(k-1), s(k)]
                    new = alteredSum $ zipWith (*) sPols ps
                in  
                upto_n (succ k) (es ++ [new])


type Q = Fraction Integer   -- LOCAL


------------------------------------------------------------------------
mToEViaP_pol_ :: CommutativeRing a => SymPol a -> Pol a
                                      -- f        h
-- Another implementation of      mToP_(pol_)
-- and an auxiliary function for  to_e_pol "mn"
-- Yields polynomial  h <- a["e"1.."e"<n>]  under lexComp ord.
-- Sometimes it is better than  mToP_,  for it avoids forming of
-- (stupidly large) Kostka matrix.
-- METHOD.
-- Like in  mToP_,  the Serret formula.  The differences are:
-- * for each sym-monomial (b,la)  of f,  (1:/1,la)  converts to
--   sym-polynomial over Q = Rational, then - to the polynomial  g(ei) 
--   over Q,  then back to  b*g <- a[e1..en],
--   the final denominators must be 1.
-- * each appearing  
--   m[1^k]       converts to  e(k),
--   m[k] = p(k)  converts to  polynomial of e(i) according to the   
--                Newton formula.                 

mToEViaP_pol_ f =  sum1 (zP: (zipWith cPMul cs hs))
 where
 n         = max (deg0 '_' 0 f) 1               -- number of vars e1..en
 vars      = map (('e' :) . show) [1 .. n]      -- say, 21-> "e21"
 (pcp, o ) = (pLexComp, lexPPO n)
 (aD, zr)  = (dom f, zeroS $ sample f)
 (un, unI, zrQ) = (unity zr, 1 :: Integer, zeroFr 0 :: Q)
 (unQ, dQ)      = (unity zrQ, upField zrQ Map.empty)
 f'             = reordSymPol pcp f
 unSPQ          = cToSymPol pcp dQ unQ           -- unity sym-pol over Q
 (zP, zPQ)       = (cToPol o vars aD zr, cToPol o vars dQ zrQ)
 (vPols, psViaE) = (varPs unQ zPQ,       powerSumsTo_e zPQ   )
                    -- e(i) as pol-s
 msg = showString 
           "\nSymmetric function transformation  mToEViaP_pol_ f " .
       showsWithDom 1 f "f" ""
 -----------------------------------------------------------------------
 -- Main loop.   Sym-polynomial over Q is given as a list of 
 -- sym-monomials (a,partition).  It converts to  h <- Q[e1..en].

 toE []                       = zPQ
 toE [(a, [])]                = ct zPQ a
 toE ((a, (k, m): q) : monsT) = 
     case (k, m, q)
     of
     (1, _, _ ) -> cPMul a $ genericIndex vPols (m-1)  -- f= a*e(m)
     (_, 1, []) -> (cPMul a $ genericIndex psViaE (pred k))+ (toE monsT)
                                                    -- f = a*p(k) + tail
     _          -> monConverted + (toE newMons)
          where  
          restDiag             = if m == 1 then q  else (k, m-1): q
          cRestI               = cFactor restDiag
          cRest                = times unQ cRestI  
          totalDivisor         = times unQ (m*cRestI)
          (ints, shiftsOfRest) = unzip $ shifts_ k restDiag
          cs = zipWith mulDiv ints $ map cFactor shiftsOfRest
                       where
                       mulDiv j k = (a*(times unQ (j*k))) / totalDivisor

          shiftsSPol = ctr unSPQ $ zip cs shiftsOfRest
          newMons    = symPolMons ((ct unSPQ monsT) - shiftsSPol)
          restMonConverted = toE [(a*cRest, restDiag)]
          monConverted =  
                     case pCDiv restMonConverted totalDivisor  
                     of
                     Just g -> (genericIndex psViaE (pred k)) * g
                     _      -> error $ msg "\n...(toE <sym-monomials>):\
                                           \  zero totalDivisor  - ?\n"
 cFactor []    = 1                          
 cFactor pairs = product $ map (factorial . snd) pairs
 -----------------------------------------------------------------------
 fromOverQ           = ctr zP . map monFromOverQ . polMons
 monFromOverQ (a, p) =  
                   if  denom a == unI  then (times un $ num a, p)
                   else
                   error $ msg ("\n...monFromOverQ " ++ (showsn 1 (a, p)
                                "\nNon-integer coefficient  (why ?)\n"))
 (cs, la_s) = unzip $ symPolMons f'
 hs         = [fromOverQ $ toE [(unQ, la)] | la <- la_s]




{- reserve *******************************************************
-- Decompose a sym-polynomial   f <- P 
-- to the polynomial            g <- P' = R[e1'..en'] 
-- of elementary symmetrics, -- n =  symPolWeight(f)
-- The result is in  lexComp  ordering  - apply (reordPol cp) if needed.
-- Method:  
-- set  Q = Fraction Integer,  decompose first the diagrams of  f 
-- over Q, then embed to P.  Namely, 
-- 1. set the  lexComp  ordering for  Ppe = Q[p1'..pn',e1'..en']  
--    and apply 
--       yDiagsToPolsOfHPS_elemSyms  (diagramsOf f) ->  hps,
--    hpi <- Ppe,  the diagram ordering in f is immaterial;
-- 2. replace  pi  in  each  hpi  with their expressions in  ei
--    (ps_via_ss),  - they have first to embed to Ppe, 
--    - and restrict (embed) the result to  Q[e1'..en'].
--    Though  hpi  have the rational coefficients, the obtained  
--    restricted  h's = [h'1,...]  must have the unity 
--    denominators, because the final symmetric decomposition of 
--    a diagram must be integer.
-- 3. Embed  h'i  to  hi  in P'  and sum up  ci*hi  in  P',   where
--    ci  are the coefficients of  f.
-- lexComp  is used to allow the more direct  substitution  and  to
-- avoid dealing with the various comparisons when embedding. 
-- The mapping between R and Q is used because the the intermediate
-- decomposition  yDiagsToPolOfHPS_elemSyms  to  pi, ej  needs 
-- division by various  k,  which may fail, for example, when 
-- Char(R)  divides  k. 

-- add something for the case  ( f = 0  or  weight(f) = 0 )
-- ********************************************************
toPolOfElemSymsOld :: CommutativeRing a =>  SymPol a -> Pol a
toPolOfElemSymsOld  f@(SymPol ymons c _) = let  
    unQ   = 1:/1  :: Q    un    = unity c   
    zr    = zeroS c       n     = symPolWeight f               
    varsP = map (('p':).show) [1..n]
    varsE = map (('e':).show) [1..n]
    varsPE = varsP++varsE           -- denotes [p1'..pn',e1'..en']
    sPols  = varPols unQ lexComp varsE           -- of Q[e1'..en']
    s1     = head sPols                     
       -- embedding from Pps to Q[e1'..en']; it is applied only to
       -- g  in which all the power products start with n zeroes
    restrict g = Pol  (map restrMon (polMons g))  unQ lexComp varsE
                 where restrMon (c,Vec js) = (c, Vec (drop n js))
    ps_via_ss  = take n (hPowerSumsAsPolsOfElemSyms s1)
                                                 -- of Q[e1'..en']
    ps_via_ss' = map (addVarsPol 'h' lexComp varsP) ps_via_ss
                                               -- embedding to Ppe
                  -- Q[any] -> R[any], the case denominators are 1
    toPolOverR  (Pol mons _ cp vs) = 
                let  mons' = [(fromi un (num r),pp)| (r,pp)<-mons]
                in   Pol (filter ((/=zr).fst) mons') c cp vs
    --------------------------------------------------------------
    (cs,diags) = unzip ymons                    -- the real method:
    hps =  yDiagsToPolsOfHPS_elemSyms lexComp varsPE diags
                                               -- hpi <- Q[varsPE]
    h's =  map  (restrict.substPsViaSs)  hps
             where  substPsViaSs h =  polSubst 'l' h ps_via_ss' []  
    rcoefss = mapmap fst $ map polMons h's
    hs      = map toPolOverR h's
  in  if  any (any (/= 1)) $ mapmap denom rcoefss
     then  error ( "DoCon SYSTEM ERROR. \n" ++
                 "toPolOfElemSyms:  some diagram decomposed to "++
                 "fractional  h'(si)  \n "           )
  else   sum1 $ zipWith cPolMul cs hs

-- probably, unnecessary *******************************************
-- Similar to previous function, only  
--                e(i) <- Pps = R[p1'..pn',s1'..sn'] 
-- which means that p(i), i = 1,2..,  are expressed via  
-- [p1..pn,s1..sn].
-- This is actually needed when i > n,  because for  i <= n
-- pi -> pi. The sample has  vars = [p1'..pn',s1'..sn']
hPowerSumsAsPolsOfPsAndElemSyms ::
                           CommutativeRing a =>  Pol a -> [Pol a]
hPowerSumsAsPolsOfPsAndElemSyms  sample@(Pol _ c cp vars) = 
  let un           = unity c    n = quot (genLength vars) 2  
    odd_n         = odd n
    (pPols,sPols) = splitAt n (varPols un cp vars)
    sPolsR        = reverse sPols
    continue (e:es) =  e:(continue (es++[new]))
      where new = let  new'= alteredSum (zipWith (*) sPolsR (e:es))
                in  if  odd_n  then new'  else (- new')
  in  continue pPols
*******************************************************************
-}



{- ***************************************************************
  problems, attempts with the NS formula 

1.
In order of symmetric decomposition, how to "extract" fast s(i)
from such diagrams like  [3,3,3], or  [i,j,k]+[1,1,1], and so on ?
Some useful extra algebraic relations needed.
2.
Failed attempt:
The above method identifies the shifted diagrams for the ones
containing the repetitions inside them:  <d++jj..j++d1>.  But many
diagrams are still processed repeatedly. For example,
      <i,j,k,l,m> ->  <i>,  <j,k,l,m>,   <i+j,k,l,m>  ...
                           /               \
                         <j>,               <i+j>,
                         <k,l,m>    <-->    <k,l,m>
                         ...              ...
To optimize this, we tried to store the current Finite Map (table)
of the values   o(diagram),   using the specially defined ordering 
(<)  on the diagrams of type (D diagram)  and the binary search in
this table. The list  hs  of the polynomials was obtained from the 
diagram list by  foldl -ing the function
          o (table,hs) diagram -> (table', h:hs)
which finds the current  h = h(diagram)   using the current  table 
value and accumulates the table and  hs:
    table0 =  listToFM  (zip  [(D [(1,i)]) | i<-[1..n]]  sPols)
                                                  -- initial table 
    o  (tab,hs) []      =  (tab, unP:hs)
    o  (tab,hs) diagram =  case  lkp tab (D diagram)  of
      (Just h) -> (tab, h:hs)
      _        ->
        let  ((k,m):pairs) = diagram
             pk       = genericIndex pExprs (k-1)
             restDiag = if  m==1  then pairs  else (k,m-1):pairs
             cRest    = cFactor restDiag   
             cTotal   = m*cRest   
             (ints,shiftsOfRest) = unzip (shifts_ k restDiag)            
             cShifts = zipWith (*) ints (map cFactor shiftsOfRest)
             coefs   = map (:/1) (cRest:cShifts)           
             (tab',hs') = foldl o (tab,[]) (restDiag:shiftsOfRest)
             (oRest:oShifts) = zipWith cPolMul coefs (reverse hs')
             g  = if  null oShifts  then  pk*oRest
                  else                 pk*oRest - (sum1 oShifts)
             g' = cPolMul (1:/cTotal) g
        in   ( addToFM tab' (D diagram) g',  g':hs )
But this did not work any faster.
3.
Future attempt.
First arrange the whole tree  T  of the diagrams that have to 
appear in the process of `o'. The factorial coefficients and the
multiplicities are stored too, and the diagrams are not repeated
in T.  T must be arranged so that it allows the cheapest 
evaluation of all  o(dg),  dg<- T  - here the order of evaluation 
is crucial. 
... the sings ?      Then proceed through T ...
******************************************************************
-}
