------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------





module Stairc_   -- Staircase form, inversion, rank  of matrix.
                 -- LinAlg.hs  reexports all necessary from here.

(reduceVec_euc, toStairMatr_euc, rank_euc, linBasInList_euc,
 inverseMatr_euc,  test_toStairMatr_euc, test_inverseMatr_euc
)
where

import qualified Data.Map as Map (empty)  

import Data.List (genericDrop, genericTake, transpose)

import DPrelude (Length(..), -- class 
                 allMaybes, evenL, mulSign, invSign, tuple31, showsn,
                                                           showsWithDom)
import Categs   (Domains1)
import SetGroup (Set(..), MulSemigroup(..), zeroS, unity)
import Ring0_   (CommutativeRing(), EuclideanRing(..), upEucRing)
import VecMatr  





------------------------------------------------------------------------
reduceVec_euc :: EuclideanRing a => Char -> [[a]] -> [a] -> ([a], [a])
                                 -- mode    us       v       rem qs
{-
The *staircase* vector list  us = [u1..un]  reduces the vector  v  as 
possible, by subtracting the linear combination of u(i).
The quotients  qs = [q1..qn]  are produced such that
                                               v = q1*u1+...+qn*un + rem
"Reducing" means making zeroes in the possibly many head positions. 
The tail of remainder it reduced too.

v, u(i)  must be of the *same size*.
mode =  'c' | ...   is as in  divRem  of EuclideanRing.
This function possesses the properties
* isZero rem  <==>  v depends linearly on `us',
* for a c-Euclidean ring,  (reduceVec_euc 'c' us) 
  is a canonical map by Submodule(us):
                                  v==v' modulo us  <==>  rem(v)==rem(v')
Method:  since `us' is staircase, only one path-through has to perform.
-}

reduceVec_euc  _     []        v = (v, [])
reduceVec_euc  mode  us@(u:_)  v = case v of a: _ -> rv (zeroS a) us v
                                             _    -> error msg 
  where
  rv zr _                []     = ([], map (const zr) us      )
  rv _  []               xs     = (xs, []                     )
  rv zr ([]: _)          xs     = (xs, zr: (map (const zr) us))
  rv zr ((y: row): rows) (x:xs) = 
    if 
      y == zr then let rowsT      = map tail rows
                       (xs', qs') = rv zr (row: rowsT) xs
                   in  (x: xs', qs')
    else
    let (q, x')    = divRem mode x y
        q_row      = map (q *) row 
        xs'        = if q == zr then xs  else  zipWith (-) xs q_row
        (xs'', qs) = rv zr (map tail rows) xs' 
    in  (x': xs'', q: qs)

  msg = concat 
        ["reduceVec_euc ", [mode], 
         " vecs v,\n\nv =  []:   non-empty  v <- Vector R  needed.\n",
         "Here  length vecs = ",  shows (genLength us) 
         ",\n  head vecs =  ", showsn 1 u msg'
        ]
  msg' = case concat us of 
                       []  -> "\n"
                       a: _-> showString "\nR =  " $ showsDomOf 1 a "\n"
  

{- ---------------------------------------------------------------------
   This is the simplified version provided as  commentary.
   Study first this source.
   The full version is      toStairMatr_euc   - see below.

strCase :: EuclideanRing a => [[a]] -> [[a]]

-- Staircase Form  of matrix  mt.
-- Only for an  Euclidean ring  a  - so far.
-- Method:
-- Gauss method applied to the Rows of  mt.  Though  a  may be not a
-- field, we repeat the remainder division to obtain zeroes down in the
-- column. 

strCase mt = let {zr = zeroS (mtHead mt);  un = unity zr}
             in
             if  isZeroMt mt  then  mt  else  scm zr un mt

  where  -- Main loop.   m  is non-empty and non-zero.
         -- Below we operate mostly with the Row Lists.
         -- Clear the first column, store row1,  cut row1 and 
         -- the first column; apply recursively  scm;  restore
         -- first zeroes and prepend row1.

  scm zr un m = sc m
    where
    sc [row] = [row]
    sc m     =
      let  m'@(row1:_) = clearColumn m    -- m'mt ==m'
      in
      case (genLength row1, (head row1) == zr)  
      of                                -- (head row1)==zr  means that
                                        -- the first column is zero
      (1, _   ) -> m'
      (_, True) -> map (zr:) $ sc $ map tail m'
      _         -> row1:(map (zr:) $ sc $ map tail $ tail m') 
                                       
                              -- here  m'(1,1)==gcd(column)/=zero,
                              -- m'(i,1)==zero  for i>1

            -- clearColumn m --> m'  
            -- From the start,  length(m) > 1.
            -- m'(1,1) = gcd(firstColumn(m)), m'(i,1)==zr  for i>1.
            -- m'(1,1)==zr  means the column was zero.

    clearColumn m = 
      case  partition (\ row -> (head row) /= zr) m  
      of
      ([]  , rest) -> rest           -- zero column
      ([r] , rest) -> r:rest         -- single non-zero
      (maxs, rest) -> c maxs rest    -- maxs are the rows with
                                     -- the non-zero head. 

            -- Each  ai = maxs(i,1)  is non-zero,  
            -- The subcolumn (a1,a2) reduces to the form (b,zero) by
            -- the Euclidean gcd algorithm,  and the transformation  
            -- matrix  t2  2x2  is accumulated. Then  t2  applies to 
            -- tail(maxs(1)), tail(maxs(2)),  and  maxs(2)  moves to
            -- rest.  This continues while  length(maxs) > 1.

    c [r]            rest = r: rest
    c (r1: r2: maxs) rest =
      let
        d            = Map.empty  :: Domains1 a
        (a1, a2, t2) =
                     reducePair (head r1) (head r2) [[un, zr], [zr, un]]
                                                             -- a2 == zr
        Mt [r1Tl,r2Tl] _ = (Mt t2 d) * (Mt [tail r1, tail r2] d)
      in
      c ((a1: r1Tl): maxs) ((a2: r2Tl): rest)

           -- reducePair a b [row1,row2] -->  (a',b',[row1',row2'])  
           --
           -- a,b  are divided repeatedly with  remainder,  like  in 
           -- extended gcd method.  [row1,row2] is a protocol matrix
           -- 2 x 2  initiated with the unity matrix.
    reducePair a b [row1,row2] =
      let  
        (q,r) = divRem '_' b a
        row2' = if  q == zr  then  row2  
                else 
                case  map (q *) row1  of qrow1 -> zipWith (-) row2 qrow1
      in
      if r == zr then  (a, r, [row1, row2'])
      else             reducePair r a [row2',row1]
-}





------------------------------------------------------------------------
toStairMatr_euc ::  
     EuclideanRing a => String -> [[a]] -> [[a]] -> ([[a]], [[a]], Char)
                        -- mode   m        t0        s      t      sign


{-   *** See first the  strCase  source. ***

Presumed:  (Euclidean(a), Yes).

The transformations are applied parallelwise to the matrix  t.

t  is the Transformation matrix, height(t) = height(m).
   If  t0 = unityMatrix  then
                         t*m = s,   where  t  is the protocol matrix
                                    for the Gauss reductions of  m,
   generally:  u*m  = s,   
               u*t0 = t    for the (invertible) protocol matrix u.

   t0 = []  is a synonym for the  Unity matrix  of size height(m).

If  m  is zero and  t0 = [],  then  (m,[])  is returned.

mode == "" | "u"
  
  "u"  means that m is *already staircase*,  and the function only tries
       to reduce to zero the elements *super the main diagonal*.
   In this case   (s1,t)  are returned where
                          s1  has reduced (*as possible*) upper part.
                          s1  is  * diagonal if  m  is invertible *. 
sign == '+' | '-'
        is the accumulated *signum* of the result row permutation.
        It is true that  ( det(m)==det(s) or det(m)== -det(s) ).
        sign  shows which of these alternatives take place.
        Thus the `det' function make use of this signum result.
        For the  "u"  mode,  sign  is always  '+'.
-}


toStairMatr_euc mode mM mT =
  (case  
       (mM, concat $ map concat [mM,mT])
   of
   ([],        es) -> error $ msg es "\nmM = [].\n"
   ([]: _,     es) -> error $ msg es "\nmM = ([]: _).\n"
   ((a: _): _, es) -> toS (msg es) (zeroS a) (unity a) (isZeroMt mM)
  )
  -- see  msg  in the end of this `where'
  where
  (hm, wm) = (mtHeight mM, mtWidth mM)

  toS _   _  _  True = (mM, mT, '+')   -- zero M
  toS msg zr un _    =
    let 
      t0   = if  null mT  then  scalarMt mM un zr  else  mT
      ht   = mtHeight t0
      msg' = showString "First row of  mM =  " . showsn 1 (head mM) . 
             showString "\n\n"
    in
    (case (hm, ht == hm, mode == "" || mode == "u")  
     of
     (1, True , _    ) -> (mM, t0, '+')
     (_, False, _    ) -> 
                error $ msg $ msg' $
                showString "height(mM) /= height(mT) = " $ shows ht "\n"

     (_, _    , False) -> error $ msg $ msg'
                                  "mode  may be only  \"\" or \"u\" \n"
     _                 ->
                    if null mode then  sc '+' mM t0
                    else              
                    (rs, rst, '+')  where  (rs, rst) = redUpper zr mM t0  
    ) 
    where                                  -- sc m t --> (m1,t1),
                                           -- m  non-empty, non-zero
    sc sg [row] [rowT] = ([row], [rowT], sg)
    sc sg m     t      =
      let  
        (m', t', sg') = clearColumn sg m t
        (r, rt)       = (head m', head t')
      in
      case (mtWidth m', head r == zr)
      of
      (1, _   ) -> (m', t', sg')
      (_, True) -> (map (zr :) s'', t'', sg'')
                              where 
                              (s'', t'', sg'') = sc sg' (map tail m') t'

      _         -> (r: (map (zr :) s''),  rt: t'', sg'')
                where
                (s'', t'', sg'') = sc sg' (map tail $ tail m') (tail t')
               
                                  
    clearColumn sg m t =               -- sg -> m -> t --> (m', t', sg')
      case  
          part (\ (row, _)-> head row /=zr) $ zip m t
                        -- yields partition 
                        -- and the permutation signum - see `part' below
      of
      ([],        restPairs, sg') -> (m', t', mulSign sg sg')
                                              where
                                              (m', t') = unzip restPairs 
      ([(r, rt)], restPairs, sg') -> (r: m', rt: t', mulSign sg sg')
                                            where
                                            (m', t') = unzip restPairs
      (maxPairs, restPairs, sg') ->
                       c (mulSign sg sg') maxs smalls tm ts (evenL maxs)
                                          where
                                          (maxs,   tm) = unzip maxPairs
                                          (smalls, ts) = unzip restPairs

          -- The below `c' differs from one from strCase in that  t2
          -- applies also to the rest of  t   and in that `c' also
          -- processes the sign.
          -- The first two elements in the first column reduce 
          -- mutually, then the reduced zero-head row goes to
          -- smalls.  The sign of this permutation is expressed by
          -- ev :: Bool.  
          -- This continues until  maxs  becomes a singleton.

    c sg [r]          smalls [rt]         ts _  = (r:smalls, rt:ts, sg)
    c sg (r1:r2:maxs) smalls (rt1:rt2:tm) ts ev =
      let
        (a1, a2, t2, sg') = 
                 reducePair '+' (head r1) (head r2) [[un, zr], [zr, un]]

        d                   = Map.empty  :: Domains1 a
        (Mt [r1Tl, r2Tl] _) = (Mt t2 d)*(Mt [tail r1, tail r2] d)
                                    -- note:  tail r1, .. may occur [] !

        (Mt [rt1', rt2'] _) = (Mt t2 d)*(Mt [rt1, rt2] d)
        sg''                = mulSign ev $ mulSign sg sg'
      in
      c sg'' ((a1: r1Tl): maxs) ((a2: r2Tl): smalls)
             (rt1'      : tm  ) (rt2'      : ts    ) (invSign ev)


    -- '+' -> a -> b -> [row1, row2] --> (a', b', [row1', row2'], sign)
              
    reducePair sg a b [row1, row2] = 
      let
        (q, r) = divRem '_' b a
        row2'  = if q == zr then row2  
                else             zipWith (-) row2 $ map (q *) row1
      in
      if r == zr then (a, r, [row1, row2'], sg)
      else            reducePair (invSign sg) r a [row2', row1]

                        -- part p xs --> (xs1,xs2,sign)
                        -- xs1,xs2 are like in standard `partition',
                        -- sign  is the permutation signum.
    part p xs =  
      let                               -- `par' also forms the evenness
        par []      = ([], [], '+', '+')     -- flag for  length(xs1)
        par (x: xs) = 
               let (xs1, xs2, sg, evn) = par xs 
               in
               if p x then (x: xs1, xs2,    sg,             invSign evn)
               else        (xs1,    x: xs2, mulSign sg evn, evn        ) 
                                                -- x jumped over xs1 ...
        (xs1, xs2, sg, _) = par xs 
      in
      (xs1, xs2, sg)

  msg es = showString 
           (concat ["toStairMatr_euc ", mode, " mM mT,\nmM is  ",  
                    shows hm " x ", shows wm 
                    ",\nmM, mT  matrices over the ring  R"]
           ) . msg' es . showChar '\n'
           where  
           msg' []     = id
           msg' (e: _) = showString " =  " . showsDomOf 1 e


------------------------------------------------------------------------
redUpper:: EuclideanRing a => a -> [[a]] -> [[a]] -> ([[a]], [[a]])
                           -- zero s        t         s1     t1
-- LOCAL.
-- See comments on  toStairMatr_euc  on the case  mode=="u".
-- Here  s  is already staircase.

redUpper _  [r] [rt] = ([r], [rt])
redUpper zr s   t    =
  let
    (nzPairs, zPairs) = break (all (== zr) . fst) $ zip s t
                                                   -- separate zero rows
    (zS, t') = unzip zPairs
    (s1, t1) = unzip $ reverse $ ru $ reverse nzPairs
                                  -- ru  is for the case of no zero rows
  in  
  (s1 ++ zS, t1 ++ t')
    where
         -- Here  s,t  are reversed and their rows are paired,
         -- s  is free of zero rows.
         -- Process the  tail(s)  recursively to  s', t';
         -- Clear the column down the first step  s2,  starting with 
         --   t',  i.e. map  bi -> bi mod b,  the rows of  s  and  t
         --   acting parallelwise;
         -- rebuild the result.

    ru [r_rt]         = [r_rt]
    ru ((r, rt): s_t) =
      let  
        zs       = takeWhile (== zr) r
        zsL      = genLength zs
        r2       = genericDrop zsL r
        s'_t'    = ru s_t
        s'1      = map (genericTake zsL) $ fst $ unzip s'_t'
        s'2_t'   = [(genericDrop zsL r, rt) | (r, rt) <- s'_t']
        s''2_t'' = map (reduceRow (head r2) r2 rt) s'2_t'
      in
      (r, rt): (zipWith (\ r1 (r2, rt)-> (r1 ++ r2,rt))  s'1  s''2_t'')

    reduceRow b row rowT (x:row1, rowT1) = 
            let
               q = fst $ divRem '_' x b 
            in
            if q == zr then  (x: row1, rowT1)
            else             (zipWith (-) (x: row1) $ map (q *) row,
                              zipWith (-) rowT1     $ map (q *) rowT)
 

------------------------------------------------------------------------
rank_euc :: EuclideanRing a => [[a]] -> Integer

rank_euc  []            = error "\nrank_euc [].\n"
rank_euc  ([]: _)       = error "\nrank_euc ([]: _).\n"
rank_euc  m@((e: _): _) =  
                      let z         = zeroS e
                          s         = tuple31 $ toStairMatr_euc "" m [] 
                          nonZeroes = fst $ span (any (/= z)) s 
                      in  genLength nonZeroes


------------------------------------------------------------------------
linBasInList_euc :: EuclideanRing a => [[a]] -> ([Bool], [[a]])
                                                          -- st
  -- For the matrix  M = [v1..vn],  mark some vi that constitute 
  -- some maximal linearly independent subset M1 in M.   
  -- In the returned  [b1..bn],  bi = True  means  vi <- M1.
  -- Also  st  is returned, the staircase form for M1.

linBasInList_euc  []             = error "\nlinBasInList_euc [].\n"
linBasInList_euc  ([]: _)        = error "\nlinBasInList_euc ([]: _).\n"
linBasInList_euc  mM@((a: _): _) = lb [] [] mM
  where
  z = zeroS a
  lb marks st []       = (reverse marks, st)
  lb marks st (v:rest) =  
    let                           -- st is staircase form for current M1
      (v', _) = reduceVec_euc '_' st v 
      iszero  = all (== z) v'
      st'     = if iszero then  st  
                else        tuple31 $ toStairMatr_euc "" (st ++ [v']) []
    in
    lb ((not iszero):marks) st' rest


------------------------------------------------------------------------
test_toStairMatr_euc :: EuclideanRing a => String -> [[a]] -> String
test_toStairMatr_euc                       mode      m     =   

                                      -- mode is as in  toStairMatr_euc
  concat ["\nStaircase form  S =\n\n", s_str, eq_str, "\n\n"]
  where
  a         = head (head m)
  d         = upEucRing a Map.empty
  (s, t, _) = toStairMatr_euc mode m []
  t_by_m    = mtRows ((Mt t d)*(Mt m d))
  s_str     = shows (Mt s d) ""
  eq_str    = if  t_by_m == s  then  "\n\nT x M = S   O.K."
              else                   "\n\nERROR:  T x M /= S "


------------------------------------------------------------------------
inverseMatr_euc :: EuclideanRing a => [[a]] -> [[a]]

  -- Inversion of square matrix  mM  over a Euclidean ring.
  -- If  mM  is invertible, the inverse matrix  iM     is returned,
  -- otherwise                                  []  
  -- Method.
  -- The Gauss reduction to the staircase form  (s,t)  is applied,  
  -- t  the transformation matrix,  t0 = unityMatrix.
  -- This reduces the task to the inversion of a  *lower-triangular*
  -- matrix.

inverseMatr_euc  []             = error "\ninverseMatr_euc [].\n"
inverseMatr_euc  ([]:_)         = error "\ninverseMatr_euc ([]: _).\n"
inverseMatr_euc  mM@((a: _): _) =  
  let
    d            = upEucRing a Map.empty
    (zr, un, mT) = (zeroS a, unity a, transpose mM)
    unM          = scalarMt mM un zr

    -- here mM is square and non-zero

    invm mM |  isLowTriangMt mM = invTriang mM unM
            |  isLowTriangMt mT = transpose $ invTriang mT unM
            |  otherwise        =                  
                          let (mS, mT, _) = toStairMatr_euc "" mM unM
                                                         -- mT*mM = mS
                              tS = transpose mS
                              tU = transpose $ invTriang tS unM
                                                           -- U*tS=unM
                          in  mtRows ((Mt tU d)*(Mt mT d))
  in
  case (isZeroMt mM, mtHeight mM == mtWidth mM)
  of
  (True, _    ) -> []
  (_,    False) -> error $ showString "\ninverseMatr_euc mM,\n" $
                           showsWithDom 1 a "mtHead mM" ""
                                        "\na SQUARE matrix needed\n"
  _             -> invm mM


------------------------------------------------------------------------
invTriang :: CommutativeRing a => [[a]] -> [[a]] -> [[a]]
                                -- inverse for a lower-triangular matrix
invTriang mM mT =  
  maybe                                    -- find [inv(d)| d<-diagonal] 
      [] (\ iDiags -> invtr iDiags mM mT) $
         allMaybes $ map inv_m $ mainMtDiag mM
    where
    invtr [ai]      _       [trow]      = [map (ai *) trow]
    invtr (ai: ais) (_: rs) (trow: trs) =  
          let
              quots           = [ai*(head r) | r <- rs]
              trowQuot        = map (ai *) trow
              reduceRow q row = zipWith (\ x y -> x - q*y) row trow
              trs'            = zipWith reduceRow quots trs 
          in  trowQuot: (invtr ais (map tail rs) trs')


------------------------------------------------------------------------
test_inverseMatr_euc :: EuclideanRing a => [[a]] -> String
test_inverseMatr_euc m =  
  case m 
  of
  []            -> error "\ntest_inverseMatr_euc [].\n"
  []: _         -> error "\ntest_inverseMatr_euc ([]: _).\n"
  m@((a: _): _) ->
     case inverseMatr_euc m  
     of
     []      -> "\nNon-invertible matrix.\n"
     im_rows ->
       "\nThe Inverse matrix  im  for  m  is \n\n" ++ (im_str ++ eq_str)
       where
       d        = upEucRing a Map.empty
       mM       = Mt m d
       iM       = Mt im_rows d
       (zr, un) = (zeroS a, unity a)
       uRows  = scalarMt im_rows un zr
       unM    = Mt uRows d
       m_im   = mM*iM
       im_m   = iM*mM
       im_str = shows iM ""
       eq_str = if im_m == unM && m_im == unM  then
                        "\n\nim*m == m*im == unity matrix  O.K.\n\n"
                else    "\n\nERROR: im*m  or  m*im /= unity matrix.\n\n"

