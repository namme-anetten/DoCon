------------------------------------------------------------------------
------------------------------------------------------------------------
--  The  Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,     2012
------------------------------------------------------------------------
------------------------------------------------------------------------




module GBasEuc_

  -- Groebner basis for the e-polynomials over an Euclidean ring.
  -- See first  GBasFld_.hs.
  --
  -- All needed from here is  reexported by  gBasis.

 (gbas_ev_, isgbas_ev_)

where
import qualified Data.Map as Map (insert, fromList, map)  

import Data.Maybe (fromMaybe)    

import DPrelude (Length(..), -- class 
                 Z, PropValue(..), allMaybes, minBy, sortBy, mapmap)
import Categs     (Property_GCDRing(..), GCDRingTerm(..))
import SetGroup   (MulSemigroup(..), isZero, unity, divides)
import RingModule (CommutativeRing(), EuclideanRing(..), GCDRing(..), 
                                                         eucGCDE)
import PP_    (PPComp, ppDivides, ppMutPrime)
import UPol_  (PolLike(..), Mon, lc, cPMul)
import Pol_   (Pol(..), monLcm)
import EPol0_ (EPol(..), eLm, eLpp, epolLCoord, eppoECp, epolECp)
import EPol1_ (EPVecP, sEPVecP)
import PolNF_ (polNF_e, polNF_ev)
import GBasFld_   
       (f_No_, cnAs_ev_, redOnePath_ev_, redToStableLpps_ev_, 
        removePair_ev_, ev_polsHaveSameCoord_, messgGBasEV_
       )






------------------------------------------------------------------------
-- PRELUDE 

-- See first  GBas_.hs


type Row a           = [(Z, Mon a)]    
type CriticalPairs a = [(Row a, Z)]

                                     -- monomial (a,p) divides (b,q)
monDivides :: MulSemigroup a => Mon a -> Mon a -> Bool
monDivides                  (a, p) (b, q) = ppDivides p q && divides a b
------------------------------------------------------------------------
minimalPair :: Eq a => PPComp -> CriticalPairs a -> ((Z, Z), Mon a)
                                                    -- i j   tTij
minimalPair            cp        dD =   
                                           -- tTij is minimal by cp
  let l2 (_, mon1) (_, mon2) =  cp (snd mon1) (snd mon2)
  in
  case [(minBy l2 row, k) | (row, k) <- dD]
  of
  []  -> error "GBasEuc_.minimalPair cp []\n"
  dD' -> minBy l2 [((i, j), mon) | ((i, mon), j) <- dD']


-- blocks -> (i,j,o)  such that (o,Tij) is minimal by ecp of Tij

minimalPair_ev ecp indBlocks =
  let         
    indBlockMin (block,o) = (ij, (o, tT))
                                 where
                                 (ij, (_, tT)) = minimalPair cp_o block
                                 cp_o p q      = ecp (o, p) (o, q)
    l2 (_, p) (_, q) = ecp p q
    ((i, j), (o, _)) = case  map indBlockMin indBlocks  
                       of
                       []  -> error "GBasEuc_.minimalPair_ev ecp []\n"
                       bls -> minBy l2 bls
  in (i, j, o)
------------------------------------------------------------------------
f_m_criterion :: CommutativeRing a => Row a -> Row a

  -- remove the Tit -s multiple for the other Ti't -s   
  -- - until this multiplicity is eliminated.

f_m_criterion row = case  row  of

  []          -> []
  [pair]      -> [pair]
  (pair: row) ->
         let mon   = snd pair
             row'  = filter (not . monDivides mon . snd) row
             row'' = f_m_criterion row'
         in
         if  any (\ (_, m) -> monDivides m mon) row''  then row''
         else                                               pair:row''
------------------------------------------------------------------------
-- differs from the field case in that Tij are the monomials, 
-- and it deals with the monomial equality, division, lcm

b_criterion_ev fsM mon block = 
                          filter (not . null . fst) $ map b_forRow block
  where
  b_forRow (row, j) =
    let
      tTj          = lm $ fst $ fst $ f_No_ fsM j
      tTkj         = monLcm mon tTj
      monDividesTj = monDivides mon tTj

                                    -- associated monomials are the ones
      nonAssocMons (a, p) (b, q) =  -- that differ in invertible factor 
                       p /= q  
                       ||
                       (case divide_m a b 
                        of  
                        Nothing -> True
                        Just c  -> (eucNorm c) /= (eucNorm $ unity a)
                       )
      b (i, tTij) = let tTi  = lm $ fst $ fst $ f_No_ fsM i
                        tTki = monLcm mon tTi
                    in
                    nonAssocMons tTki tTij  && nonAssocMons tTkj tTij
                    &&
                    (monDividesTj || monDivides mon tTij)
    in
    (filter (not . b) row, j)
------------------------------------------------------------------------
monMutPrimeInv :: EuclideanRing a => Mon a -> Mon a -> Bool

  -- "mutually prime" criterion:
  -- the critical pair (f,g) is skipped if
  --   lpp(f), lpp(g)   are  mutually prime
  --   and
  --   lc(g), lc(h)  are invertible  
  --                    (have the same Euclidean norm as the unity).
  --   
  -- This criterion is NOT applied for the vectors of dim > 1.

monMutPrimeInv (a, p) (b, q) = 
                             ppMutPrime p q 
                             && (eucNorm a) == unN && (eucNorm b) == unN
                                               where
                                               unN = eucNorm $ unity a

{-# specialize monMutPrimeInv :: Mon Z -> Mon Z -> Bool #-}
------------------------------------------------------------------------
-- This  updatePairs  differs from the one of the field case in that
--   the criteria are for the critical pairs containing monomials,
--   isRedex  processing is skipped so far.

updatePairs_ev applyPPMutPrime fsM indBlocks t =
  let
    f        = fst $ f_No_ fsM t
    (o, mon) = (epolLCoord $ fst f, lm $ fst f)
    row      = [(i, f_No_ fsM i) | i <- [1 .. (t-1)]]

                                      -- filter out redexes and items of
                                      -- the different head coordinate 
    row00 = filter (not . snd . snd) row
    row'  = [(i, f) | (i, (f, _)) <- row00]
    row'o = filter ((== o) . epolLCoord . fst . snd) row'
    row0  = 
       if  not applyPPMutPrime  then  row'o
       else [x| x <- row'o, not $ monMutPrimeInv mon $ lm $ fst $ snd x]

    row'' = [(i, tTit f) | (i, f) <- row0]  where  
                                            tTit = monLcm mon . lm . fst
    row1  = f_m_criterion row''
    irowL = if  null row1  then []  else [(row1, t)]
  in 
  case (row1, span ((/= o) . snd) indBlocks)      
                                  -- find block_o and apply b_criterion
  of
  ( [], (indBs, []                ) ) -> indBs
  ( _ , (indBs, []                ) ) -> (irowL, o): indBs
  ( _ , (indBs, (block, _): indBs') ) ->  
                let               
                   blockL = case  (row1, b_criterion_ev fsM mon block)
                            of                     
                            ([], []    ) -> []
                            (_,  block') -> [(irowL ++ block', o)]
                       
                in  indBs ++ (blockL ++ indBs')


repeatUpdatePairs_ev_euc applyPPMutPrime indBs fsM =  
                        foldl (updatePairs_ev applyPPMutPrime fsM) indBs

------------------------------------------------------------------------
redOnePath_euc_ev ::  
                   EuclideanRing a => String -> [EPVecP a] -> [EPVecP a]

  -- Reduce  fi  with respect to each other.
  -- It is applied in  Groebner basis  only once,  in the end  -  to 
  -- obtain a reduced weak GB.
  -- This is more complex than in the Field case.
  -- For this  *commentary*,  let us forget of the coordinate and of 
  -- the vector parts of  f(i)  from  fs:
  -- for each  f,  hs = [g <- fs| lpp g  divides  lpp f].
  -- Let  f1 = linear combination of hs over `a'  such that 
  --                                     lc f1 = gcd [lc h| h <- hs]
  -- Reduce each  g <- fs  by  polNF mode [f1]   and obtain  fs'  by 
  -- removing zeroes. Then continue with  f1:fs'  choosing the 
  -- starting  f  different from  f1.  And so on.  
  -- One path-through applies.

redOnePath_euc_ev mode fs =  redt [] fs   
  where
  redt fs []     = fs 
  redt fs (f:gs) = 
    let                                           -- f is "under" (i, p)
      under (i, p) f =  i == j && ppDivides q p
                                            where  (j, q) = eLpp $ fst f

      dividesEM (a, (i, p)) f =  i == j && monDivides (a, p) (b, q) 
                                           where 
                                           (b, (j, q)) = eLm $ fst f

      evplus (f, u) (g, v) =  (f+g,       zipWith (+) u v)
      cEVMul c      (f, v) =  (cPMul c f, map (cPMul c) v)

      ep           = eLpp $ fst f
      hs           = f: (filter (under ep) (fs ++ gs))
      (_, qs)      = eucGCDE $ map (lc . fst) hs
      f1           = foldl1 evplus $ zipWith cEVMul qs hs
      em1          = eLm $ fst f1
      [fs',  gs' ] = map (filter (not . dividesEM em1)) [fs, gs]
      [fs'', gs''] = mapmap (polNF_ev mode [f1]) [fs', gs']
    in
    redt (f1:fs'') gs''


-- END PRELUDE
------------------------------------------------------------------------





gbas_ev_ :: EuclideanRing a => [EPVecP a] -> [EPVecP a]

  -- Weak reduced Groebner basis  for non-zero polynomials  
  -- over an Euclidean GCD-ring `a'.
  --
  -- See first  GBas_hs, GBasFld_.hs.  
  -- and  [Mo] Moeller  "On the Construction of Groebner Bases ...".
  -- 
  -- The method differs from the field case in that
  -- * for the critical pairs, the monomials are processed, not only 
  --   the power products,
  -- * the polNF reduction is weak: it solves each time the linear 
  --   equation on monomials.
  --   
  -- From the final algorithm of [Mo],  it differs in that it  finds 
  -- the weak Groebner basis - it does *not process the completion*.
  --
  -- Concerning the possible strong basis, see the end of this file.

gbas_ev_ fs =  
  let
    processPairs _       _   []        _ gs = gs
    processPairs singleC fsM indBlocks r gs =  
      let
        ecp        = epolECp $ fst $ head gs
        (i, j, oC) = minimalPair_ev ecp indBlocks
        [fi, fj]   = map (fst . f_No_ fsM) [i, j]
        (h', _ ,_) = fromMaybe 
                     (error $ messgGBasEV_ fs "GBasEuc_.gbas_ev_" msg) $
                     {- SCC "sp_euc"$ -}  sEPVecP fi fj

        h   = {- SCC "polNF_ev_euc"$ -}  polNF_ev "" gs h'

        msg = "\n... sEPVecP f_i f_j -> Nothing  for some i,j \n"
      in
      if  isZero $ fst h  then                                  
                   processPairs  
                      singleC fsM (removePair_ev_ indBlocks i j oC) r gs
      else          
      let r'          = r+1
          (a, (o, p)) = eLm $ fst h
          gs'         = h: (filter (not . eLmRedex) gs)
                                                -- newCompletion_ev gs h
          eLmRedex (g, _) = case eLm g 
                            of 
                            (b, (o', q)) ->
                                     o == o' && monDivides (a, p) (b, q)

          markRedex (f, redt) = (f, redt || eLmRedex f)

          fsM'       = Map.insert r' (h, False) fsM
          indBlocks' = updatePairs_ev  singleC fsM' indBlocks r'
          fsMr       = Map.map markRedex fsM
          fsM''      = Map.insert r' (h, False) fsMr
      in
      processPairs singleC fsM''
                              (removePair_ev_ indBlocks' i j oC)  r' gs'
    --------------------------------------------------------------------
  in
  case redToStableLpps_ev_ Nothing fs  
  of
  []  -> []
  [f] -> [f]
  fs  -> 
    let EPol _ eo pol  = fst $ head fs
        ecp            = eppoECp eo
        Pol _ c _ _ aD = pol
        (_, gcR)       = baseGCDRing c aD
        (props, r)     = (gcdRingProps gcR, genLength fs)

        fsM = Map.fromList $ 
              zipWith (\ i f -> (i, (f, False))) [1 .. r] fs

        singleC   = ev_polsHaveSameCoord_ fs
        indBlocks = repeatUpdatePairs_ev_euc singleC [] fsM [2 .. r]

        cmpELpp f g = ecp (eLpp $ fst f) (eLpp $ fst g)

        gs  = redOnePath_ev_ "r" Nothing $ redOnePath_euc_ev "r" $
                                 processPairs singleC fsM indBlocks r fs
        gs' = sortBy cmpELpp gs
    in
    case  lookup WithCanAssoc props  of Just Yes -> map cnAs_ev_ gs'
                                        _        -> gs'



------------------------------------------------------------------------
isgbas_ev_ :: EuclideanRing a => [EPVecP a] -> Bool

  -- See  isGBasis, isGBasis_e, gBas_euc_ev.
  --
  -- Here  fs  is free of zeroes and non-empty.

isgbas_ev_ fvs =  case  redToStableLpps_ev_ Nothing fvs  of

  []  -> True
  [_] -> True
  fvs -> 
    let r   = genLength fvs  
        fsM = Map.fromList $ 
              zipWith (\ i fv -> (i, (fv, False))) [1 .. r] fvs

        singleC   = ev_polsHaveSameCoord_ fvs
        indBlocks = repeatUpdatePairs_ev_euc  singleC [] fsM [2 .. r] 
        fs        = map fst fvs

        trivialRow fsM fs (row, j) =  
          let
            fvj      = fst $ f_No_ fsM j
            fvi_s    = map (fst . (f_No_ fsM)) $ map fst row
            triplets =
                fromMaybe 
                  (error $ messgGBasEV_ fvs "GBasEuc_.isgbas_ev_" msg) $
                  allMaybes $ map (sEPVecP fvj) fvi_s

            sepols = [fst h | (h, _, _) <- triplets]
            msg    = "\n...(map (sEPVecP fvj)..)  contains Nothing\n"
          in
          all isZero $ map (fst . polNF_e "" fs) sepols
    in
    all (all (trivialRow fsM fs) . fst) indBlocks
