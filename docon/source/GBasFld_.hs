------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------





module GBasFld_ 

  -- Groebner basis for e-polynomials over a field.
  -- Here and in GBasEuc_  it is contained the real implementation
  -- for the Groebner basis.
  -- All needed from here is  reexported by  GBasis.

(gBas_field_ev_, isGBas_field_ev_,

 -- exported only for  GBasEuc_, Polrel_:
 f_No_, redCan_ev_, redOnePath_ev_, redToStableLpps_ev_, cnAs_ev_,
 ev_polsHaveSameCoord_, removePair_, removePair_ev_, messgGBasEV_
)  
where
import qualified Data.Map as Map 
                        (Map(..), lookup, insert, toList, fromList, map)

import Data.Maybe (fromMaybe) 
import Data.List  (nub)

import DPrelude (Length(..), -- class 
                 Natural, allMaybes, sortBy, minBy, showsn, 
                                                    showsWithDom)
import SetGroup   (Set(..), isZero, inv)
import RingModule (GCDRing(..), EuclideanRing(..))
import PP_        (PowerProduct, PPComp, ppLcm, ppDivides, ppMutPrime)
import UPol_      (PolLike(..), lc, cPMul)
import EPol0_     (EPPComp, epolMons, eLpp, epolLCoord, epolECp)
import EPol1_     (EPVecP, sEPVecP)
import PolNF_     (polNF_e, polNF_ev)







------------------------------------------------------------------------
-- Groebner basis  for  Non-zero polynomials over a field.
--
-- The core method follows the paper [GM]
-- Gebauer, Moeller  "On Installation of Buchberger's Algorithm".
--
-- Look this paper through to get the general idea and to  apprehend
-- denotations.
--
-- DIFFERENCE:
-- in  updatePairs,  we do not find so totally reduced D1'  as the paper
-- does 
-- (by the way, the paper typos in this place badly, so that D1' 
--  always occurs empty !).
-- Instead, we apply the  "mutually prime", F- and M- criteria -- which 
-- agrees with the air of the paper.
--
-- And we join F- and M- criteria into one  f_m_criterion  which simply 
-- removes the Tit -s multiple for the other Ti't -s - until this 
-- multiplicity is eliminated.
------------------------------------------------------------------------
-- OTHER DETAILS.
--
-- Critical pair set structure.
--
-- For the efficiency, the current set D of the critical pairs is 
-- organized into the list of indexed rows:
--
-- D =  [(row_j1,j1) ... (row_jr,jr)],   j1 > ... > jr >= 2,
--                                                   empty rows skipped,
--
-- row_j = [ (i_1, T(i_1,j)) ... (i_kj, T(i_kj,j)) ],  
--                                            1 =< i_1 < ... < i_kj < j,
-- 
-- The program takes care to maintain this ordering.
-- So the  critical pair  has the form  (i, Tij)
-- (index j is common for the whole row)  where 
--                                   i < j,  Tij = lcm(lpp(fi),lpp(fj)).
------------------------------------------------------------------------
-- F and G lists.
-- First  fi  from fs reduce each other until there is no  fi  has 
-- reducible  Ti = lpp (fi).
--
-- The obtained new list  fs  transforms into the 
--   list   G      which grows to the Groebner basis in the end,
--                 and serves to reduce all the intermediate 
--                 s-polynomials,
--   finite map (table)  
--              fsM  representing F = {f1,...,fr},  the set which is 
--                   the source of the critical pairs.  
-- Access to  fi:    f_No_ fsM i  ->  (fi,isRedex),
--
-- isRedex = True    means that  fi  became redundant  (by some 
--                   newly obtained  fj,  j > r >= i.  Such  fi
--                   is skipped in the further generations of D1'
--                   - see the paper.  Also these redexes are 
--                   removed from  gs.
--
-- In the paper, fi  form an array and are accessed by the index.
-- It may cause a great complication to re-implement the method
-- relying only on the usual lists.
-- So we store fi in the table - *finite map*  that is implemented
-- in the Haskell library pure functionally, as an expression 
-- represented by a binary tree (we could easily program this in 
-- Haskell ourself). This map is better than array because we do not
-- bother for bounds.
-- The cost of accessing to  fi = f_No_ table i  is more than f[i]
-- for an array in the C language, but in this algorithm this cost 
-- is immaterial.
------------------------------------------------------------------------
-- The main loop is called  processPairs.  
-- It finds the pair (i,j) in D (selectPair)  which has the smallest 
-- Tij  relatively to the  cp  ordering on the power product, and 
-- reduces its  s-polynomial to  h.
-- If this new  h  is non-zero, it
--   removes its redexes from G and joins  fsM, 
--   forms separately the critical pair row  row2  for  h,  
--   removes the b_criterion pairs for h from D, making D',
--   prepends row2 to D', obtaining newD,
--   marks the redexes of  h  (except h itself)  in  fsM,
--   removes the pair of (i,j) from newD.
------------------------------------------------------------------------
-- This commentary concern the case of *polynomials*.  The function
-- actually implemented is  gBasis_e  that deals with the 
-- *e-polynomials*.
------------------------------------------------------------------------






------------------------------------------------------------------------
-- PRELUDE  for the Groebner basis function.
--
-- The below functions are shared partially between
-- gBas_field_ev_, polRelGens
--
-- The function names with the _ev suffix refer to  gBas_field_ev_
-- - see the comments on this function.


-- type FinMap_ a = Map.Map Natural (Pol a, Bool)

type Row           = [(Natural, PowerProduct)]
type CriticalPairs = [(Row, Natural)]

------------------------------------------------------------------------
f_No_ :: Set a => Map.Map Natural (a, Bool) -> Natural -> (a, Bool)   
                                            -- tab-> i-> (f(i), isRedex)
f_No_ tab i = case  Map.lookup i tab  of  
                                      Just x -> x 
                                      _      -> error $ msg $ msg' ".\n"
  where
  msg = showString "\ngBasis fs  for the list of PolLike things ...\n\n\
                   \f_No_ table " . shows i .
        showString ":   index not found in  table.\ntable  contains the\
                   \ items (j, (f, bool)) with (j, bool) <-\n" . 
                                                       showsn 1 tab'List
  tabList  = Map.toList tab
  tab'List = [(i, b) | (i, (_, b)) <- tabList]
  msg'     = 
         case tabList 
         of 
         []             -> id
         (j, (f, b)): _ -> showString "\nThe head item is  (j, (f, b)),\
                                      \ (j, b) = " .
                           shows (j, b) . showsWithDom 1 f "f" ""

------------------------------------------------------------------------
cnAs_ev_ :: GCDRing a => EPVecP a -> EPVecP a
cnAs_ev_ (f, fs) =  
         if  isZero f  then (f, fs)
         else
         let {a = lc f;  ii = inv $ canInv a}
         in  if  a == canAssoc a  then  (f, fs)
             else                       (cPMul ii f, map (cPMul ii) fs)

------------------------------------------------------------------------
redCan_ev_ :: 
     (GCDRing a, EuclideanRing a) =>  
     String -> Maybe (EPVecP a -> EPVecP a) -> [EPVecP a] -> EPVecP a ->
                                                             EPVecP a 
-- In the field case, this is always called with  (Just cnAs_ev_).
-- In non-field-Euclidean case, it is called with  Nothing  in the 
-- intermediate evaluation and once in the end with 
-- Just cnAs_ev_   - if only `a' has (WithCanAssoc, Yes).

redCan_ev_ mode mbCnAs gs =  fromMaybe id mbCnAs . polNF_ev mode gs 

                                         -- shorthand for the field case
justCnAs :: GCDRing a => Maybe (EPVecP a -> EPVecP a)
justCnAs = Just cnAs_ev_   

------------------------------------------------------------------------
redOnePath_ev_ :: 
      (GCDRing a, EuclideanRing a) =>  
      String -> Maybe (EPVecP a -> EPVecP a) -> [EPVecP a] -> [EPVecP a]

                            -- mode -> fs -> mayBeCanAssoc -> fs_reduced
                            -- reduces fi with respect to each other
redOnePath_ev_ _    _      [] =  [] 
redOnePath_ev_ mode mbCnAs fs =  redt [] fs   
  where
  redt rs []      = rs 
  redt rs (f: fs) =  
    let  
      r = -- SCC "redCan_ev_" $ 
          redCan_ev_ mode mbCnAs (rs ++ fs) f
    in
    if  isZero $ fst r  then  redt rs fs  else  redt (r: rs) fs

------------------------------------------------------------------------
redToStableLpps_ev_ ::                -- reduce until  lpp-s  are stable
   EuclideanRing a =>
   Maybe (EPVecP a -> EPVecP a) -> [EPVecP a] -> [EPVecP a]

redToStableLpps_ev_ mbCnAs fs =  rtos fs $ map (eLpp . fst) fs
  where
  rtos fs lpps = let fs'   = reverse $ redOnePath_ev_ "" mbCnAs fs
                     lpps' = map (eLpp . fst) fs'          
                 in  if lpps' == lpps then  fs'  else  rtos fs' lpps'

------------------------------------------------------------------------
minimalPair :: 
           PPComp -> CriticalPairs -> ((Natural, Natural), PowerProduct)
           -- cp     dD                (i, j)              tTij
-- tTij  is minimal by cp
-- The below  selectPair - minimalPair  optimization is good even 
-- for the lexComp  ordering. Thus the "discrim" test becomes much 
--                                                            cheaper.
minimalPair cp dD = 
             let l2 (_, p) (_, q) = cp p q
                 dD'              = [(minBy l2 row, k) | (row, k) <- dD]
             in  minBy l2 [((i, j), p) | ((i, p), j) <- dD']

------------------------------------------------------------------------
selectPair_ev :: 
    EPPComp -> [(CriticalPairs, Natural)] -> (Natural, Natural, Natural)

-- blocks -> (i, j, o)   such that (o, Tij)  is  ecp-minimal  of  Tij

selectPair_ev ecp indBlocks = (i, j, o)
  where
  indBlockMin :: (CriticalPairs, Natural) -> 
                           ((Natural, Natural), (Natural, PowerProduct))
  indBlockMin (block, o) = (ij, (o, tT))
                                      where  
                                      (ij, tT)  = minimalPair cp_o block
                                      cp_o p q  = ecp (o, p) (o, q)
  l2 (_, p) (_, q) = ecp p q
  ((i, j), (o, _)) = minBy l2 $ map indBlockMin indBlocks

------------------------------------------------------------------------
type GenericRow a = [(Natural, a)]
--
-- a = PowerProduct  for  Field a,  Mon a  for non-field-Euclidean a. 
-- Similar is with CriticalPairs.
--
type GenericCriticalPairs a = [(GenericRow a, Natural)]

removePair_ :: 
  GenericCriticalPairs a -> Natural -> Natural -> GenericCriticalPairs a

-- Remove the critical pair of (i, j) from dD.
-- It also removes the row if the row turns empty.  
-- We skip the type, for this has to work for dD in the Euclidean case
--                                                                too.
removePair_ crps i j =  
  case crps 
  of  
  []              -> []
  (row, j'): rows ->        
    if 
      j' /= j  then  (row, j'): (removePair_ rows i j)
    else  
    (case  rmFromRow row  of  []   -> rows
                              row' -> (row', j): rows
    )
    where  
    rmFromRow []             = []
    rmFromRow ((i', x): row) = if  i == i'  then  row 
                               else             (i', x): (rmFromRow row)


removePair_ev_ :: 
     [(GenericCriticalPairs a, Natural)]-> Natural-> Natural-> Natural->
                                     [(GenericCriticalPairs a, Natural)]
-- \ indBlocks i j o --> indBlocks'
-- It also removes the row if the row turns empty; the same is with the
--                                                                block.
removePair_ev_ indBlocks  i j o =  
  case indBlocks 
  of
  []             -> []
  (b, o'): indBs ->
         if o' == o then  case removePair_ b i j of [] -> indBs
                                                    b' -> (b', o): indBs
         else             (b, o'): (removePair_ev_ indBs i j o) 

------------------------------------------------------------------------
f_m_criterion :: Row -> Row

-- remove the Tit -s multiple for the other Ti't -s   - until this
--                                           multiplicity is eliminated.
f_m_criterion row =  
  case row 
  of
  []       -> []
  [pair]   -> [pair]
  pair:row -> let p     = snd pair
                  row'  = filter (not . ppDivides p . snd) row
                  row'' = f_m_criterion row'
              in
              if any (\ (_, q) -> ppDivides q p) row''  then row''
              else                                           pair: row''


------------------------------------------------------------------------
b_criterion_ev :: EuclideanRing a => 
                  Map.Map Integer (EPVecP a, Bool) ->          -- fsM  
                  PowerProduct                     ->          -- p
                  CriticalPairs                    ->          -- block
                  CriticalPairs                                -- block'

-- Remove from  dD  all the  pairs  (i, Tij)  such that p divides Tij  
-- and  T_p_i /= Tij  and  T_p_j /= Tij.
-- Empty rows remove, the index order preserves.
-- We use here that  * j  is common for each row,
--                   * if p divides Tj, then  p  divides all  Tij.
-- The above procedure applies to each indexed block of the 
-- critical pairs -- for the e-polynomial case.
-- It may return the empty block.

b_criterion_ev fsM p block = 
                          filter (not . null . fst) $ map b_forRow block
  where
  b_forRow (row, j) = (filter (not . b) row, j)
       where
       tTj = lpp $ fst $ fst $  f_No_ fsM j
                                             -- ((epol, pols), boo)
       tTpj         = ppLcm p tTj
       p_divides_Tj = ppDivides p tTj
       b (i, tTij)  = let tTi  = lpp $ fst $ fst $ f_No_ fsM i
                          tTpi = ppLcm p tTi
                      in  tTpi /= tTij  &&  tTpj /= tTij  &&
                          (p_divides_Tj || ppDivides p tTij)
   

------------------------------------------------------------------------
-- Updating the set of the critical pairs.
-- This is the core of the Groebner basis algorithm. 
-- Here are contained the optimizations.
--
-- See the paper to apprehend denotations.

{- This is a commentary. -----------------------------------------------
The real function is  updatePairs_ev:  see below.

updatePairs :: Map_ a -> CriticalPairs -> Natural -> CriticalPairs
updatePairs    fsM       dD               t =
  let
    f = fst $ f_No_ fsM t   -- f = f_t
    p = lpp f  
                                     -- form the row of the critical
                                     -- pairs for the new f
    row   = [(i, f_No_ fsM i) | i <- [1..(t-1)]]
    row0  = filter (not .snd .snd) row             -- remove redexes
    row00 = [(i,f) | (i,(f,_)) <- row0]
    row'  = filter (not .ppMutPrime p .lpp .snd) row00

    row'' = [(i,tTit f) | (i,f) <- row']  where
                                            tTit f = ppLcm p (lpp f)
    row1  = f_m_criterion row''
    dD'   = b_criterion  fsM p dD
                       -- independently, p filters out some critical
                       -- pairs from the previously obtained rows
  in
  if  null row1  then  dD'  else  (row1,t):dD'
------------------------------------------------------------------------
-}



updatePairs_ev :: 
                EuclideanRing a =>
                Bool                             ->   -- applyPPMutPrime  
                Map.Map Integer (EPVecP a, Bool) ->   -- fsM  
                [(CriticalPairs, Natural)]       ->   -- indBlocks
                Natural                          ->   -- t
                [(CriticalPairs, Natural)]            -- indBlocks'

-- See first the commentaries to  gBas_field_ev_
-- Here  applyPPMutPrime  means "apply ppMutPrime criterion".
--
-- It is called with   False  for the  e-polynomials of dim > 1.

updatePairs_ev applyPPMutPrime fsM indBlocks t = 
  let
    f      = fst $ f_No_ fsM t
    (o, p) = eLpp $ fst f
    row    = [(i, f_No_ fsM i) | i <- [1 .. (pred t)]]

                       -- now remove redexes and fi of L-coordinate /= o
    row0  = filter (not . snd . snd) row 
    row'  = [(i, f) | (i, (f, _)) <- row0]
    row'o = filter ((== o) . epolLCoord . fst . snd) row'
    row00 = if  not applyPPMutPrime  then  row'o 
            else 
            [x | x <- row'o, not $ ppMutPrime p $ lpp $ fst $ snd x]

    row'' = [(i, tTit f) | (i, f) <- row00]
                                     where  tTit = ppLcm p . lpp . fst
    row1  = f_m_criterion row''
    irowL = if  null row1  then []  else [(row1, t)]
  in 
  case (row1, span ((/= o) . snd) indBlocks)      
                                  -- find block_o and apply b_criterion
  of
  ([], (indBs, []                )) -> indBs
  (_,  (indBs, []                )) -> (irowL, o): indBs
  (_,  (indBs, (block, _): indBs')) -> indBs ++ (blockL ++ indBs')
                        where               
                        blockL = case (row1, b_criterion_ev fsM p block)
                                 of                     
                                 ([], []    ) -> []
                                 (_,  block') -> [(irowL ++ block',o)]
                    

repeatUpdatePairs_ev  applyPPMutPrime indBs fsM =                     
                        foldl (updatePairs_ev applyPPMutPrime fsM) indBs

------------------------------------------------------------------------
                        -- find whether all the  ev-monomials  from a
                        -- non-empty  fvs  belong to the same coordinate
ev_polsHaveSameCoord_ :: [EPVecP a] -> Bool
ev_polsHaveSameCoord_ fvs =
  let
    evpCoords = nub . map (fst . snd) . epolMons . fst
  in
  case  map evpCoords fvs  of  [j]: jss -> all (== [j]) jss
                               _        -> False

-- END OF PRELUDE
------------------------------------------------------------------------




{- This COMMENTARY -----------------------------------------------------
shows the method for the computing of a G-basis 
over a field.
The actual (local) function is  gBas_field_ev_  - see below.

gBas_field fs =  
  let
    processPairs _   [] _  gG = gG
    processPairs fsM dD rR gG =  
      let
        (_,cp,_)  = pPPO $ head gG
        ((i,j),_) = selectPair cp dD                        
        [fi,fj]   = map (fst .f_No_ fsM) [i,j]
        (h',_,_)  = sPol fi fj
        h         = redCan "" gG h'
      in
      if isZero h  then  processPairs fsM (removePair_ dD i j) rR gG
      else          
        let  rR'     = rR+1
             p       = lpp h
             p_redex = ppDivides p .lpp
             gG'     = h: (filter (not .p_redex) gG)

             markRedex (f, redt) =  (f, redt || p_redex f)

             fsM'  = Map.insert fsM rR' (h,False)
             dD'   = updatePairs fsM' dD rR'
             fsMr  = Map.map markRedex fsM
             fsM'' = Map.insert fsMr rR' (h,False)
          in
          processPairs fsM'' (removePair_ dD' i j) rR' gG'
  in
  case  redToStableLpps fs  
  of
    []  -> []
    [f] -> [canAssoc f]
    fs  -> let  r   = genLength fs  
                                                  -- fs -> map table
                fsM = Map.fromList $    
                             zipWith (\i f->(i,(f,False))) [1..r] fs
                dD  = repeatUpdatePairs [] fsM [2..r] 
           in
           redOnePath "r" $ processPairs fsM dD r fs
------------------------------------------------------------------------
-}




------------------------------------------------------------------------
-- Case of  e-VecPol-s.   
-- See  gBas_field  here,    type EPVecP ...
--
-- The critical pairs break into the independent _blocks_ 
-- according to the coordinate number  o,  and the criteria act 
-- blockwise.
-- The "mutually prime" criterion is not valid if we have more than one 
-- coordinate.
--
-- In  indBlocks = [(block_1,o1),...,(block_k,ok)]  
--
-- each block_o  contains the critical pairs organized as in the set 
--               D in  gBas_field,
--      {oi}     are all the leading coordinate numbers of the 
--               current  fs  (no repetitions among oi).
--
-- Also the e-polynomials are paired here with the polynomial 
-- vectors - this makes them the e-vec-pol-s.
-- The vector parts are used in DoCon only to accumulate the 
-- transformation matrix from the initial basis. Operations on the 
-- vector parts are "parallel" (with the same coefficients) to the ones 
-- on polynomials.


gBas_field_ev_ :: EuclideanRing a => [EPVecP a] -> [EPVecP a]

-- this local function is invocated only when  isField(a) == Yes
        
gBas_field_ev_ fs =  
  let
    processPairs _       _   []        _  gG = gG
    processPairs singleC fsM indBlocks rR gG =  
      let
        ecp        = epolECp $ fst $ head gG
        (i, j, oC) = selectPair_ev ecp indBlocks

        [fi, fj]   = map (fst . f_No_ fsM) [i, j]
        (h', _, _) = 
              fromMaybe (error $ messgGBasEV_ fs "gBas_field_ev_" msg) $
                        sEPVecP fi fj                        -- SCC "sp"

        h   = redCan_ev_ "" justCnAs gG h'           -- SCC "redCan_ev_"
        msg = "\n... sEPVecP f_i f_j -> Nothing  for some  i,j \n"
      in
      if  isZero $ fst h  then                                  
                     processPairs  
                     singleC fsM (removePair_ev_ indBlocks i j oC) rR gG
      else          
      let rR'    = succ rR
          (o, p) = eLpp $ fst h
          gG'    = h: (filter (not.o_p_redex) gG)

          o_p_redex (g, _) =  o' == o && ppDivides p q  where  
                                                        (o', q) = eLpp g
          markRedex (f, redt) = (f, redt || o_p_redex f)

          fsM'       = Map.insert rR' (h, False) fsM
          indBlocks' = updatePairs_ev singleC fsM' indBlocks rR'
          fsMr       = Map.map markRedex fsM
          fsM''      = Map.insert rR' (h, False) fsMr
        in
        -- a good place to insert things like   trace (show p) $  
        --
        processPairs singleC fsM''
                             (removePair_ev_ indBlocks' i j oC)  rR' gG'
  in
  case  redToStableLpps_ev_ justCnAs fs  
  of
  []  -> []
  [f] -> [cnAs_ev_ f]
  fs  -> let ecp = epolECp $ fst $ head fs
             r   = genLength fs           
             fsM = Map.fromList $ 
                   zipWith (\ i f -> (i, (f, False))) [1 .. r] fs

             singleC     = ev_polsHaveSameCoord_ fs
             indBlocks   = repeatUpdatePairs_ev  singleC [] fsM [2 .. r]
             cmpELpp f g = ecp (eLpp $ fst f) $ eLpp $ fst g
         in
         sortBy cmpELpp $ redOnePath_ev_ "rc" justCnAs $
                          processPairs singleC fsM indBlocks r fs

                     

messgGBasEV_ :: 
             EuclideanRing a => [EPVecP a] -> String -> String -> String
messgGBasEV_                    fs@(f: _)     funcName =

      showString (funcName ++ " fs,") . showString "\nlength fs = " . 
      shows (genLength fs) . showsWithDom 1 (fst f) "fst $ head fs" "" 


------------------------------------------------------------------------
-- See  gBas_field_ev_.
-- Here  fs  is free of zeroes and non-empty.

isGBas_field_ev_ :: EuclideanRing a => [EPVecP a] -> Bool
isGBas_field_ev_ fvs =  
  case  
      redToStableLpps_ev_ justCnAs fvs  
  of
  []  -> True
  [_] -> True
  fvs -> all (all (trivialRow fsM fs) . fst) indBlocks
    where
    r   = genLength fvs  
    fsM = Map.fromList $ 
          zipWith (\ i fv -> (i, (fv, False))) [1 .. r] fvs

    singleC   = ev_polsHaveSameCoord_ fvs
    indBlocks = repeatUpdatePairs_ev  singleC [] fsM [2 .. r] 
    fs        = map fst fvs

    trivialRow fsM fs (row, j) =  
                           all isZero $ map (fst . polNF_e "" fs) sepols
        where
        fvj      = fst $ f_No_ fsM j
        fvi_s    = map (fst . f_No_ fsM) $ map fst row
        triplets = fromMaybe
                   (error $ messgGBasEV_ fvs "isGBas_field_ev_" msg) $
                                     allMaybes $ map (sEPVecP fvj) fvi_s
        sepols = [fst h | (h, _, _) <- triplets]
        msg    = "\n... (map (sEPVecP fvj)..)  contains Nothing\n"
