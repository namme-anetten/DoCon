------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------





module SymmFn_  -- Symmetric function transformations.
                -- All needed from here is reexported by  AlgSymmF.
-- See first the commentary in the head module  AlgSymmF.

(PrttParamMatrix, SymFTransTab, SymmDecMessageMode(..), 
 ptpMatrRows, transpPtP,  h'to_p_coef, elemSymPols, hPowerSums,
 intListToSymPol, toDensePP_in_symPol, fromDensePP_in_pol,

 pToS_, hToS_, eToS_, mToS_,  msgDcSum_, msgPtLkpK_   -- local things
)
where
import Debug.Trace (trace)
import qualified Data.Map as Map 
              (Map(..), empty, lookup, findWithDefault, insert, toList, 
                                                               fromList)
import Data.Maybe (fromMaybe)
import Data.List  (transpose)

import DPrelude (Length(..), -- class 
                 Natural, Z, ct, dropAsMuch, sum1, product1, factorial, 
                 sortBy, allMaybes, showsn, showsWithDom, 
                                                       addListToMapWith)
import Categs     (Dom(..), Domains1)
import SetGroup   (zeroS, unity, times)
import RingModule (Ring(..), CommutativeRing())    

import Pol (PolLike(..), Pol(..), PolVar, PPOrdTerm, varP, upolMons, 
                                               reordPol, cToUPol, cPMul)
import LinAlg (solveLinearTriangular)
import Partition (Partition, PrttComp, pLexComp, conjPrtt, ppToPrtt, 
                  prttToPP, prevPrttOfN_lex, prttWeight, prttsOfW, 
                  kostkaColumn, kostkaTMinor, permGroupCharColumn,  
                 )
import Sympol_ (SymPol(..), symPolMons, reordSymPol, symLdPrtt, 
                                                     symPolHomogForms)





------------------------------------------------------------------------
type PrttParamMatrix a = Map.Map Partition [a]

-- a partition-parameterized matrix over `a' (ptp-matrix)
-- is a table of pairs (Partition,Row)

type SymFTransTab = 
           Map.Map Z ([Partition], PrttParamMatrix Z, PrttParamMatrix Z)
                      -- pts       tC                 tK
                                                          -- see Preface
ptpMatrRows :: PrttParamMatrix a -> [[a]]
ptpMatrRows tab =  map snd $ sortBy gtLex $ Map.toList tab
                                    where
                                    gtLex (p, _) (q, _) = pLexComp q p

transpPtP :: PrttParamMatrix a -> PrttParamMatrix a
transpPtP tab =  Map.fromList $ zip pts $ transpose rows
          where
          (pts, rows)         = unzip $ sortBy gtLex $ Map.toList tab
          gtLex (p, _) (q, _) = pLexComp q p 


------------------------------------------------------------------------
-- The construction of  pi(x1..xn),  ei(x1..xn)   
-- is NOT used in the decomposition.
-- They serve for testing and other needs.

elemSymPols :: CommutativeRing a => Pol a -> Domains1 (Pol a) -> [Pol a]
                                    -- f     dP
-- Elementary symmetric polynomials [e1..en],  ei of P = R[x1..xn],
-- built from the sample polynomial f.
-- dP is the description of P.
-- Example:  elemSymPols f (upRing f Map.empty) 
--           builds small necessary part of P, and then, [e1..en]
--            
-- Method:  let  g = (y+x1)*..*(y+xn)  of  P[y]
--          in   coefficients( pTail((y+x1)*..*(y+xn)) )

elemSymPols f dP =  tail $ map fst $ upolMons p
       where
       (vars, un) = (pVars f, unity $ sample f)
       unP        = unity f
       unPP       = cToUPol "y" dP unP
       y          = varP unP unPP
       yCopies    = map (const y) vars
       xsY        = map (ct unPP) $ varPs un f        -- x1..xn in P[y]
       p          = product1 $ zipWith (+) yCopies xsY

------------------------------------------------------------------------
hPowerSums :: CommutativeRing a => Pol a -> [Pol a]

-- homogeneous power sums  [p1,p2 .. ],  pi = x1^i +..+ xn^i
-- built from the sample polynomial

hPowerSums f = let un     = unity $ sample f
                   pwList = varPs un f    -- [x1..xn] as polynomials
                   pLists = pwList: (map (zipWith (*) pwList) pLists)
               in  map sum1 pLists    -- [[x1..xn],[x1^2..xn^2] .. ]
               

------------------------------------------------------------------------
h'to_p_coef :: Partition -> Natural
h'to_p_coef []           = 1
h'to_p_coef ((i, m): la) = (factorial m)*(i^m)*(h'to_p_coef la)
  --
  -- Coefficient  z(la)  of partition  la  in the formula
  --
  --      h(n) =  sum( (1/z(la))*p(la) |  |la| = n )
  --
  -- expressing the full homogeneous function as the rational linear
  -- combination of  p(la)   - see [Ma] 1.2 formula (2.14').
  -- Namely, 
  -- h'to_p_coef [(i1, m1) ... (il, ml)] = 
  --                       product( (i(k)^m(k))*m(k)! |  k <- [1 .. l] )
  -- This is more direct and nice than iterating Newton formula.
  -- And it is also used in the  e(n) -> p(la)  decomposition.


------------------------------------------------------------------------
toDensePP_in_symPol :: PPOrdTerm -> [PolVar] -> SymPol a -> Pol a
toDensePP_in_symPol o vars (SymPol ms c _ d) =
                                        reordPol o (Pol mons c o vars d)
  where  
  mons = [(a, prttToPP n pt) | (a, pt) <- ms]
  n    = genLength vars
  --
  -- Returns the polynomial in the given pp-ordering o  and variable
  -- list.
  -- Each partition from  symPol  converts into the power product of
  -- length  l = length(vars)  by  prttToPP;
  -- then the monomials are re-ordered with  o.
  -- Usually it is applied after  (to_<v> _ _ _).


fromDensePP_in_pol :: PrttComp -> Pol a -> SymPol a

-- Inverse to  toDensePP_in_symPol. 
-- Returns the sym-polynomial in the given partition comparison. 

fromDensePP_in_pol pcp (Pol ms c _ _ dm) =
                                  reordSymPol pcp $ SymPol mons c pcp dm
                               where  
                               mons = [(a, ppToPrtt pt) | (a, pt) <- ms]

------------------------------------------------------------------------
intListToSymPol ::  
   Ring a => 
   Char -> SymPol a -> Partition -> [Partition] -> [Integer] -> SymPol a
-- mode    smp         bound        allPts         row

-- Convert integer list  row  to sym-polynomial under pLexComp ordering
-- - considering  row  as the numeration of partitions.
-- smp  is the sample sym-polynomial (maybe, not in pLexComp).
-- row  is an integer list representing a dense homogeneous 
-- sym-polynomial over Integer of weight w > 0:
--                                f = sum( i(la)*la | la <- allPts )
-- - in pLexComp ordering.
-- allPts  is the full list of partitions of  w  ordered decreasingly by
--                                                             pLexComp.
-- f  converts to  sym-polynomial  g  over `a', mostly, by filtering out 
--    zero monomials.
-- mode = 'a'  means run through all the partitions ignoring `bound',
--        'u'  means the row is zero beyond the segment [maximal,bound],
--        'l'  ...                                      [bound,minimal].
-- This is all used for the integer vectors  row  who are computed 
--                                                             "lazily". 
intListToSymPol mode smp bound allPts row =
                                 SymPol (toSymMons prow') zr pLexComp dm
   where
   (dm, zr) = (dom smp, zeroS $ sample smp)
   un    = unity zr 
   prow  = zip row allPts
   bPrev = maybe [] id $ prevPrttOfN_lex bound
   prow' = case mode of 'a' -> prow
                        'l' -> dropWhile ((/= bound) . snd) prow
                        _   -> takeWhile ((/= bPrev) . snd) prow

   toSymMons mons = filter ((/= zr) . fst) $
                                    [(times un j, mu) | (j, mu) <- mons]


------------------------------------------------------------------------
msgDcSum_ :: CommutativeRing a => SymPol a -> String -> String -> String
                                                                -- LOCAL 
msgDcSum_ f fName = showString (concat
                          ["It calls  decompAndSum (table,res) ", fName,
                           "   with homogeneous ", fName, " =\n  "
                          ]) . 
                    showsn 1 f . showString "\n\n..."
                                                        
msgPtLkpK_ :: Partition -> String -> String -> String           -- LOCAL
msgPtLkpK_ la mtName =  
                showString (concat ["lookup failed in   ", mtName, 
                                    "(weight)  for the partition\n "]) . 
                shows la

------------------------------------------------------------------------
pToS_ :: CommutativeRing a =>
                    SymFTransTab -> SymPol a -> (SymFTransTab, SymPol a)
                    -- tab          f            tab'          h
-- METHOD:   M(p,s) = tC   the irreducible character matrix.
--
-- Each row in  tC  is produced by  permGroupCharColumn(ro) - 
-- unless it is found in the  tC(w)  part of  tab,
--       p(ro) =  Sum( C(la,ro)*s(la) |  la <- allPts )        (1)
--
-- Each homogeneous part  f(w) =  sum( c(ro)*p(ro)| ...)  
-- converts according to  (1).
-- Each character column adds to the current C(w), and new C(w)  adds to
-- tab.

pToS_ tab f =  foldl decompAndSum (tab, zeroSP) $ symPolHomogForms f'
 where 
 f'     = reordSymPol pLexComp f
 zeroSP = zeroS f'
                                -- Below f  is homogeneous and non-zero.
                                -- (tab,res) -> f -> (tab_new, res+h(f))
 decompAndSum (tab, res) f =  
            (if w == 0 then  (tab, res + f)
             else            (Map.insert w (allPts, tC', tK) tab, res'))
   where
   w                = prttWeight $ symLdPrtt f
   (allPts, tC, tK) = Map.findWithDefault 
                         (prttsOfW [(w, 1)], Map.empty, Map.empty) w tab

                           -- convert sym-monomial to sym-polynomial  
                           -- mConverted  in "s"  and add to result
                           -- accumulating  tC
   convMonAndAdd (tC, res) (c, ro) = 
          let
             col = Map.findWithDefault
                             (snd $ permGroupCharColumn ro allPts) ro tC
             mConverted = cPMul c $ intListToSymPol 'a' f' [] allPts col
                                            -- mode smp bound allPts row
          in (Map.insert ro col tC, res + mConverted)

   (tC', res') = foldl convMonAndAdd (tC, res) $ symPolMons f
 


------------------------------------------------------------------------
hToS_ :: CommutativeRing a => 
                    SymFTransTab -> SymPol a -> (SymFTransTab, SymPol a)
                    -- tab          f            tab'          h
-- METHOD:   M(h,s) = tK   the transposed Kostka matrix.
-- Each row of  tK  is produced by  kostkaColumn - unless it is 
-- found in the  tK(w)  part of the  table. Since  tK  is lower-
-- triangular,            h(la) = Sum( K(la,mu)*s(mu) | mu >= la )   (1)
--
-- Each homogeneous  f(w) = sum( c(la)*h(la)| ...) 
-- converts according to (1).
-- Each Kostka column adds to the current tK(w), and new  tK(w)  adds to 
--                                                           the  table.

hToS_ tab f =  foldl decompAndSum (tab, zeroSP) $ symPolHomogForms f'
 where
 f'     = reordSymPol pLexComp f
 zeroSP = zeroS f'
                             
 decompAndSum (tab, res) f =          -- here f is homogeneous, non-zero
             (if w == 0 then (tab, res + f)
              else           (Map.insert w (allPts, tC, tK') tab, res'))
   where
   w                = prttWeight $ symLdPrtt f
   (allPts, tC, tK) = Map.findWithDefault 
                         (prttsOfW [(w, 1)], Map.empty, Map.empty) w tab

                               -- convert sym-monomial to sym-polynomial  
                               -- mConverted  in "s" and add to result
                               --                        accumulating tK
   convMonAndAdd (tK, res) (c, la) = 
       let
          col = Map.findWithDefault (snd $ kostkaColumn la allPts) la tK
          mConverted = cPMul c $ intListToSymPol 'u' f' la allPts col
       in (Map.insert la col tK, res + mConverted)

   (tK', res') = foldl convMonAndAdd (tK, res) $ symPolMons f



------------------------------------------------------------------------
eToS_ :: CommutativeRing a => 
                    SymFTransTab -> SymPol a -> (SymFTransTab, SymPol a)
                    -- tab          f            tab'          h
-- METHOD:   M(e,s) = tK*J
-- So, it differs from  hToS_  only in that each row of  tK  is 
-- being transposed according to index partition conjugation.
-- Also the segment is not defined inside the row.

eToS_ tab f =  foldl decompAndSum (tab, zeroSP) $ symPolHomogForms f'
 where
 f'     = reordSymPol pLexComp f
 zeroSP = zeroS f'                            
 decompAndSum (tab, res) f =          -- here f is homogeneous, non-zero

             (if w == 0 then (tab, res + f)
              else           (Map.insert w (allPts, tC, tK') tab, res'))
   where
   w                = prttWeight $ symLdPrtt f
   (allPts, tC, tK) = Map.findWithDefault 
                         (prttsOfW [(w, 1)], Map.empty, Map.empty) w tab 
   pt's            = map conjPrtt allPts
   conjugateRow xs = map snd $ sortBy gtLex $ zip pt's xs
                                      where
                                      gtLex (p, _) (q, _) = pLexComp q p 

                               -- convert sym-monomial to sym-polynomial  
                               -- mConverted  in "s"  and add to result
                               --                        accumulating tK
   convMonAndAdd (tK, res) (c, la) = 
        let
          col = Map.findWithDefault (snd $ kostkaColumn la allPts) la tK
          cnjRow     = conjugateRow col
          mConverted = cPMul c $ intListToSymPol 'a' f' [] allPts cnjRow
        in
        (Map.insert la col tK, res + mConverted)

   (tK', res') = foldl convMonAndAdd (tK, res) $ symPolMons f



------------------------------------------------------------------------
data SymmDecMessageMode = DoSymmDecMessages Integer | NoSymmDecMessages
                          deriving (Eq, Show)
--
-- This mode may be usable because some partitions take too long to
-- decompose.

mToS_ :: 
  CommutativeRing a => 
  SymmDecMessageMode -> SymFTransTab -> SymPol a -> 
                                                (SymFTransTab, SymPol a)
  -- msgMode            tab             f        tab'          h

-- METHOD:  M(m,s)  is by solving the system  xRow x K = indVec(la).
-- Here  indVec(la)  is the vector with 1 on the position of  la  and 
-- 0 on other positions. K  is the Kostka matrix -- which is 
-- upper-triangular and has 1 on the main diagonal.
-- The table is used like in  sToH_.

mToS_ msgMode tab f = 
                  foldr decompAndSum (tab, zeroSP) $ symPolHomogForms f'
 where
 f'     = reordSymPol pLexComp f
 zeroSP = zeroS f'
 msg    = showString "\nSymmetric bases transformation  mToS_ " .  
          shows msgMode . showString " table f" .
           showsWithDom 1 f "f" ""
                             
 decompAndSum f (tab, res) =           -- here f is homogeneous, non-zero 

            (if  w == 0  then  (tab, res + f)            -- case deg = 0
             else              (Map.insert w (allPts, tC, tK) tab, res'))
   where
   w                 = prttWeight $ symLdPrtt f
   (allPts, tC, tK') = Map.findWithDefault  
                          (prttsOfW [(w, 1)], Map.empty, Map.empty) w tab

                                                          -- see  s_to_h
   forcedPRows = zip allPts $ kostkaTMinor allPts allPts
   tK          = addListToMapWith (\ old _ -> old) tK' forcedPRows
   tKRows = fromMaybe (error $ msg $ msgDcSum_ f "fh"
                             "Kostka matrix  tK  (from table)  \
                             \wrongly completed (why ?)\n"
                      ) $ allMaybes [Map.lookup p tK | p <- allPts]

   strictness = minimum $ map minimum tKRows
                                   -- because in this order the elements 
                                   --        of tK are evaluated cheaper
   mK = seq strictness $ transpose tKRows        

        -- iK = let rs = inverseMatr_euc tKRows            -- for test 
        --      in  transpPtP $ Map.fromList $ zip allPts rs
                                  
   convMon (c, la) =               -- convert SymMon to SymPol in "s" by 
          (case msgMode            -- solving  xRow x K = indVec_la
           of
           NoSymmDecMessages    -> id
           DoSymmDecMessages w' ->              
               if  prttWeight la < w'  then  id
               else
               trace ("mToS_:  decomposing sym-mon with the partition  "
                      ++ (show la))
          ) $  
          cPMul c $ intListToSymPol 'l' f' la allPts (zeroes ++ xs)

           -- test =  case  Map.lookup la iK  of
           --   Just row -> cPMul c $ intListToSymPol 'l' f' la allPts 
           --                                               row
           --   _ ->
           --   error $ msg $ msgDcSum_ f "fh" $ msgPtLkpK_ la "iK" "\n"

          where
          (ptsBefore, _: ptsAfter) = span (/= la) allPts
          zeroes                   = map (const 0) ptsBefore
          cutK = map (dropAsMuch ptsBefore) $ dropAsMuch ptsBefore mK
            --
            -- This is an optimization: cutK is the tail main minor 
            -- corresponding to the part of indVec(la) starting with la,
            -- the head part of mK corresponds to first zeroes in  xVec. 

          indVec_la_cut =  1: (map (const 0) ptsAfter)
          xs = fromMaybe 
               (error $ msg $ concat 
                ["no solution for the Kostka system for  ", shows la 
                 ".\nWhat may be the error?\n"]
               ) $
               solveLinearTriangular cutK indVec_la_cut
   ----------------------------------------------------------------
   res' = foldr (+) res $ map convMon $ symPolMons f

