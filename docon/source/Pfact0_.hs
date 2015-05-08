------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------



module Pfact0_  -- Polynomial factorization.
                -- * generic Hensel lift;
                -- * test for factorization over finite field;
                -- * auxiliary functions for factorization in  k[t][x], 
                --   k  a finite field.
                -- All needed from here is reexported by Pol.

(vecLDeg, henselLift, testFactorUPol_finField,
 smallInLattice_triang_    -- henselLift_test
)
where
import qualified Data.Map as Map (empty) 

import Data.Maybe (fromJust)
import Data.List  ((\\), partition, transpose, genericSplitAt)

import Prelude hiding(maximum)

import DPrelude (Length(..), -- class
                 Natural, sum1, maximum, minBy, maxBy, sortBy, ct, ctr, 
                                           mapmap, showsn, showsWithDom)
import Categs   (Dom(..), ResidueE(..), OSet(..))
import SetGroup (Set(..), AddSemigroup(..), MulSemigroup(..), zeroS,
                 unity, isZero, unfactor 
                )
import RingModule (Ring(..), CommutativeRing(), EuclideanRing(..),
                   GCDRing(..), FactorizationRing(..), Field(), 
                   remEuc, eucGCDE, eucIdeal, upRing, upField
                  )
import VecMatr  (mtHeight, rowMatrMul, scalarMt)
import ResEuc0_ (Residue(..)                   )
import ResEuc_ ()
import RsePol_ () 
import UPol_   (PolLike(..), UPol(..), upolMons, deg0, lc, varP, cPMul,
                                                                cToUPol)
import Pol__   (RPolVar)
import RPol_   (RPol(..), RPol'(..), rpolRepr, rpolVComp, rpolHeadVar, 
                         rpolVars, cToRPol, varToRPol, substValsInRPol)
import RPol0_ () 







------------------------------------------------------------------------
vecLDeg :: (PolLike p, AddSemigroup (p a), CommutativeRing a) => 
                                             Integer -> [p a] -> Integer
vecLDeg d = maximum . map (deg0 'l' d)

------------------------------------------------------------------------
henselLift ::                            --OI**
 (EuclideanRing a, FactorizationRing a, Ring (ResidueE a))
 =>
 UPol a -> UPol a -> UPol a -> Maybe (UPol a) -> a -> a -> Natural -> 
                                                               Natural->
 -- f      h1        g1        v1                p    p^n  n  m

                                            (UPol a, UPol a, UPol a, a)
                                             -- h'   g'      v'      p^m

-- Denote  Fk = a/(p^k),  rk: a[x] -> Fk[x]  natural projection.
-- Given 
--   a square free  f  from  A[x],  
--   a prime  p  from A,  p  does not divide  resultant f f'  
--     (hence  deg r1(f) = deg f,  r1(f) is square free),
--   h1, g1, v1, n  such that   f - h1*g1 <- (p^n),
--                              v1 = (f - h1*g1)/(p^n),
--                            0 < l = deg h1 < deg f,  lc(h1) = 1,
--   m >= n,
-- find  (h',g',v',p^m)  such that
--   f - h'*g' <- (p^m),   v' = (f - h'*g')/(p^m),
--   deg h' = deg h1, deg g' = deg g1,   lc(h') = 1,  |h'|,|g'| < n*|p|.
--
-- Denotations:  F = F1 = a/(p),  R = F[x],  pp = p^k, rpp = rk,
--               deg = deg_x,  |.| = (deg_t .).
-- The below algorithm has the degree cost in  |p|, deg f.
-- See  theory.txt  for more comments.

henselLift f h1 g1 mbV1 p pp n m = 

 (case (p == zr || eucNorm p == minNorm,  any isZero [f, h1])
  of
  (True, _   ) -> error $ msg "p = 0:  a prime p required.\n"
  (_,    True) -> error $ msg degmessg
  _            -> 
                 case (lc h1 == un, deg f, deg h1) 
                 of
                 (False, _ , _ ) -> error $ msg "lc h = 1  required\n"
                 (_,     df, dh) -> 
                   if  df <= dh || dh <= 0  then  error $ msg degmessg
                   else              
                   case (n > 0, compare n m)
                   of
                   (False, _ ) -> error $ msg "n < 1 \n"
                   (_,     EQ) -> (h1, g1, v1, pp)
                   (_,     GT) -> error $ msg "n <= m  required\n"
                   _           -> repeatBy1 n (h1, g1, v1, toR v1, pp/p)
 )
 where
 divByCoef f = fromJust . pCDiv f 
 remByCoef a = pMapCoef 'r' (\ b -> remEuc 'c' b a) 
 (dA, x)  = (dom f, head $ pVars f)   -- dA === `a'
 (zr, un) = (zeroS p, unity p)
 minNorm  = eucNorm un
 v1       = case mbV1 of Just v -> v
                         _      -> 
                                 remByCoef pp $ divByCoef (f - h1*g1) pp
 iI    = eucIdeal "be" p [] [] [(p, 1)]
 toF a = Rse (remEuc 'c' a p) iI dA     -- a -> F 
 zrF   = toF zr
 unF   = unity zrF 
 dF    = upField unF Map.empty
 r1    = cToUPol x dF unF                             -- 1 of R
 toR f = ctr r1 [(toF a, e) | (a, e) <- upolMons f]   -- a[x] -> R

 fromR g    = ct f [(resRepr r, e) | (r, e) <- upolMons g]
 (h1R, g1R) = (toR h1, toR g1)
 h0R        = let (gc, u:_) = eucGCDE [g1R, h1R] 
              in               -- decompose  1 = h0R*g1R + g0R*h1R  in R
              case inv_m gc 
              of
              Just ig -> ig*u
              _       -> 
                   error $ msg
                   "\ngcd (g mod p) (h mod p)  occurs not invertible.\n\
                   \Probably,  (f mod p)  is not square free.\n"
 msg = showString "\nhenselLift f h g v p n m,\n" . 
       showsWithDom 1 p "p" "R" . 
       showString "\nf =  " . showsn 1 f  . showString "\nh =  " . 
       showsn 1 h1 . showString "\ng =  " . showsn 1 g1 . 
       showString "\nf, h, g <- R[.] =  " . showsDomOf 1 f  . 
       showString "\n:\n"
 -----------------------------------------------------------------------
 lift1 h g v vR pp' = (h', g', v', v'R, pp)
      where
      hcR         = remEuc '_' (vR*h0R) h1R  -- hcR*gR + (.)*hR = vR
      gcR         = (vR - hcR*g1R)/h1R
      (hc, gc)    = (fromR hcR, fromR gcR)
      (pp, pp'hc) = (p*pp', cPMul pp' hc)
      (h', g')    = (h + (cPMul p pp'hc), g+(cPMul pp gc))
      v'1         = divByCoef (v - hc*g - h*gc) p
              -- because 
              -- v' = (f-h'*g')/(p*pp) = 
              -- (f - h*g - pp*(hc*g + h*gc) - pp^2*hc*gc) /(p*pp) =
              -- ((f - h*g)/pp - hc*g - h*gc - pp*hc*gc) /p  
              --
      v'  =  v'1 - pp'hc*gc
      v'R =  if  pp' == un  then  toR (v'1 - hc*gc)  else  toR v'1
 -----------------------------------------------------------------------
 repeatBy1 n (h, g, v, vR, pp') = 
                                 if n == m then  (h, g, v, p*pp') 
                                 else 
                                 repeatBy1 (succ n) $ lift1 h g v vR pp'

 degmessg = "0 < deg h < deg f  required.\n"






{- old ****************************************************************
henselLift ::                                     --OI**
        (EuclideanRing a, FactorizationRing a, Ring (ResidueE a)) =>
           a -> UPol a -> UPol a -> UPol a -> [(UPol a,UPol a)]
henselLift p    f         h1        g1     =     let
    divByCoef f = fromJust . pCDiv f 
    (dA, x) = (dom f, head $ pVars f)   -- dA === `a'
    (zr,un) = (zeroS p, unity p)
    minNorm = eucNorm un
    iI      = eucIdeal "be" p [] [] [(p,1)]
    toF a   = Rse (remEuc 'c' a p) iI dA     -- a -> F 
    zrF     = toF zr
    unF     = unity zrF 
    dF      = upField unF Map.empty
    r1      = cToUPol x dF unF                          -- 1 of R
    toR f   = ctr r1 [(toF a,e) | (a,e) <- upolMons f]  -- a[x] -> R
    fromR g   = ct f [(resRepr r,e) | (r,e) <- upolMons g]
    (h1R,g1R) = (toR h1, toR g1)
    h0R       = let  (gc,u:_) = eucGCDE [g1R,h1R] 
                in   case  inv_m gc  of  Just ig -> ig*u
                                         _       -> error ..
    v1  = divByCoef (f - h1*g1) p
    ----------------------------------------------------------------
    hl pp' h g v vR = (h',g'):(hl pp h' g' v' v'R)
      -- Main loop.
      -- Here  pp = pp'*p = p^k, vR = toR v, (f-h*g)/pp = v <- A[x].
      -- h,g  reduced modulo  pp.
      -- hl  yields  (h',g'):(hl (p*pp) g' h', v'R),  where
      -- f  = g'*h' (mod p*pp),  |g'|,|h'| < |p*pp|,
      -- h' = h + pp*hc,       |hc| < |p|, deg hc < l = deg h1, 
      -- g' = g + pp*gc,       |gc| < |p|, deg gc <= deg g = deg g1,
      -- v' = (v - h*gc - g*hc - pp^2*hc*gc)/p
      -- According to  theory.txt,  deg v <= n,  and  
      -- hc = h0*v mod h1, gc = (v-hc*g)/h  - with  h0,g0  as above.
      where
      hcR        = remEuc '_' (vR*h0R) h1R   -- hcR*gR + (.)*hR = vR
      gcR        = (vR-hcR*g1R)/h1R
      (hc,gc)    = (fromR hcR, fromR gcR)
      (pp,pp'hc) = (p*pp', cPMul pp' hc)
      (h',g')    = (h + (cPMul p pp'hc), g+(cPMul pp gc))
      v'1        = divByCoef (v - hc*g - h*gc) p
              -- because 
              -- v' = (f-h'*g')/(p*pp) = 
              -- (f - h*g - pp*(hc*g + h*gc) - pp^2*hc*gc) /(p*pp) =
              -- ((f - h*g)/pp - hc*g - h*gc - pp*hc*gc) /p  
      v'  = v'1 - pp'hc*gc
      v'R = if  pp'==un  then  toR (v'1-hc*gc)  else  toR v'1
  in case  (p==zr || (eucNorm p)==minNorm,  any isZero [f,h1]) of
    (True, _   ) -> error $ msg "p = 0:  a prime p required\n"
    (_   , True) -> error $ msg degmessg
    _            -> 
      case  (lc h1 == un, deg f, deg h1)  of
        (False, _, _) -> error $ msg "lc h = 1  required\n"
        (_    , n, m) -> 
                 if  n <= m || m <= 0  then  error $ msg degmessg
                 else                        hl un h1 g1 v1 (toR v1)

henselLift_test :: 
      EuclideanRing a =>
      a -> UPol a -> UPol a -> UPol a -> [(UPol a,UPol a)] -> [Bool]
    --p    f         h         g         pairs         
henselLift_test p f h g pairs = map test $ zip (ppowers (p^2)) pairs
  where  ppowers pp        = pp:(ppowers (p*pp))
  test (pp, (h, g)) = let opp = eucNorm pp  in
                      isJust (pCDiv (f-h*g) pp)
                      &&  order h < opp  &&  deg h == dH 
                      && lc h == un && order g < opp  &&  deg g == dG 
  (un, dH, dG) = (unity p, deg h, deg g)
  order        = maximum . map (eucNorm . fst) . upolMons
*********************************************************************
-}



{- Experiment: quadratic lift  ***************************************
to be improved ...
improve the  x- degrees in  h',g'...Something is totally wrong here
henselLift ::                       
  (EuclideanRing a, FactorizationRing a, Ring (ResidueE a)) =>
  UPol a-> UPol a-> UPol a-> UPol a -> UPol a -> a -> a -> Z -> Z ->
  -- f     h1       g1       hc1       gc1       p    pp   n    m
                              (UPol a, UPol a, UPol a, UPol a, a, Z)
                               -- h'   g'      hc1'    gc1'   pp' n'
  -- Hensel lift of factorization   f = g1*h1 
  -- from  pp = p^n  to  pp' = pp^n', n' = n*2^k,  
  -- k = min [k | n*2^k >= m].
  -- f - g1*h1    <- (pp),    1 - gc1*h1 - hc1*g1    <- (pp)
  -- f - g1'*h1'  <- (pp'),   1 - gc1'*h1 - hc1'*g1  <- (pp')
henselLift f h1 g1 hc1 gc1 p pp n m =  let
    divByCoef f = fromJust . pCDiv f 
    (zr,un)     = (zeroS p, unity p)    minNorm     = eucNorm un
    u1          = divByCoef ((unity f) - gc1*h1 - hc1*g1) pp
    v1          = divByCoef (f - h1*g1) pp
    ----------------------------------------------------------------
    liftToSquare (h,g,hc1,gc1,u,v,pp) = (h',g',hc1',gc1',u^2,v',pp2)
      where
      -- u  = (1 - gc1*h  - hc1*g) /pp                 <- a[x]
      -- v  = (f - h*g)/pp                             <- a[x]
      -- u' = (1 - gc1'*h - hc1'*g)/(pp^2)  = u^2 (?)  <- a[x]   
      -- v' = (f - h'*g')/pp^2                         <- a[x]
      remByCoef a = pMapCoef 'r' (\b-> remEuc 'c' b a) 
      pp2  = pp^2
      hc1' = remByCoef pp2 $ upolPseudoRem (hc1+(cPMul pp (u*hc1))) h1
                                              --substitute u(gc1..)?
      gc1' = remByCoef pp2 $ upolPseudoRem (gc1+(cPMul pp (u*gc1))) g1
      hc = upolPseudoRem (v*hc1) h1;  gc = upolPseudoRem (v*gc1) g1
      h' = remByCoef pp2 (h + (cPMul pp hc))
      g' = remByCoef pp2 (g + (cPMul pp gc)); v' = u*v - hc*gc  -- ?
    ----------------------------------------------------------------
    repeatLiftToSquare n (h,g,hc1,gc1,u,v,pp) =
      if n >= m  then  (h,g,hc1,gc1,pp,n)
      else repeatLiftToSquare (2*n) $ liftToSquare (h,g,hc1,gc1,u,v,pp)
    degmessg = "0 < deg h < deg f  required\n"
  in case  (p==zr || (eucNorm p)==minNorm,  any isZero [f,h1]) of
    (True, _   ) -> error $ msg "p = 0:  a prime p required\n"
    (_   , True) -> error $ msg degmessg
    _            -> case  (lc h1 == un, deg f, deg h1)    of
        (False, _ , _ ) -> error $ msg "lc h = 1  required\n"
        (_    , df, dh) -> 
          if  df <= dh || dh <= 0  then  error $ msg degmessg
          else case  (n < 1, n > m) of
              (True, _   ) -> error $ msg "n < 1 \n"
              (_   , True) -> error $ msg "n > m \n"
         _            -> repeatLiftToSquare n (h1,g1,hc1,gc1,u1,v1,pp)
-}



------------------------------------------------------------------------
testFactorUPol_finField :: Field k => UPol k -> [Bool]

-- Test  partially  factorization for polynomial  f  from  k[x],  
-- k  a finite field.
-- f is factored to  ps = [(p(1),n(1))...],  and it is tested that 
--   (canAssoc f)==(product [p(i)^n(i)...]),  
--   p(i)  are reciprocally prime,
--   for each i  isPrime p(i), non-linear p(i) has not root in  k.

testFactorUPol_finField f =  tf (zeroS $ sample f) (dom f) (canAssoc f) 
  where
  tf k0 dK cf =  
     case  osetList $ snd $ baseSet k0 dK  
     of
     Nothing    -> error ("\ntestFactorUPol_finField f," ++ 
                          (showsWithDom 1 f "f" "k[x]" 
                           "\nFinite listing for  k  not found.\n"))
     Just kList -> 
              let pairs   = factor f
                  ps      = map fst pairs
                  nonLins = filter ((> 1) . deg) ps
              in
              [cf == unfactor pairs, 
               all isPrime ps,
               recipPrime ps,       
               all (/= k0) [pValue f [a] | f <- nonLins, a <- kList]
              ]
            where
            recipPrime (f: fs) = all (== 0) [deg $ gcD [f, g] | g <- fs]
            recipPrime _       = True


------------------------------------------------------------------------
smallInLattice_triang_ ::
         Field fF =>
         UPol fF -> Natural -> Natural -> [[UPol fF]] -> Maybe [UPol fF]
         -- pp      l1         bound      mH
  -- LOCAL.
  -- Used only in  factorOverFinField_2_.
  -- Search for sufficiently small non-zero vector  b  in lattice  L
  -- over  A = F[t]  given by a triangular  m1 x m1  matrix over  A 
  -- of kind                   E | H         = B1
  --                      B =  ---------
  --                           00| pp*E'     = B2,
  -- |pp| = deg pp > 0,
  -- E,E'  are the unity matrices of sizes  ml',l1,   m1 > l1 > 0,
  -- 00    zero matrix,  H  has elements  h(i,j),  |h(i,j)| < |pp|.
  --
  -- Searched is  b  such that   |b| =def= max [|b(i)|...] <= bound.
  -- The search may return  Nothing.
  -- METHOD  [Me3, 'pr.h0_sv'].
  -- Briefly:  if there exists  b  in  L  such that  |b| <= bound,
  -- then it can be found as  u*B,  u <- A^m1, |u| <= bound.
  -- Hence,  |u*B| <= bound  expresses as the linear system with the
  -- finite set of unknowns  u(i)(j) <- F,  u = [u(1)..u(m1)].

smallInLattice_triang_ pp l1 bnd mH = 
 let
   --------------------------------------------------------------------
   (opp, ml') = (deg pp, mtHeight mH)   -- (|p|*k, m+1-l1),
   m1         = l1+ml'                -- m+1, l1, m  are from
                                      -- factorization method [Me3,'a']
   (zrA, unA) = (zeroS pp, unity pp)
   mE         = scalarMt mH unA zrA
   (minE, minVInH) = minBy cp $ zip mE mH    
                 where                  -- row in H,B1 of minimal order
                 cp (_, u) (_, v) = compare (vecLDeg 0 u) (vecLDeg 0 v)

   maxsH = map (vecLDeg 0) $ transpose mH  
                                       -- maximal order for each column
   bnsR  = map boundFor1 maxsH
                           -- bounds  deg u(i) <= bn(i)  for  i > ml'.
                           -- While for  i <= ml',  bn(i) = bnd.
                           -- bn(i) are used only when  |minVInH| > bnd
                    where
                    boundFor1 max1 = let bn' = bnd + max1 - opp
                                     in  if  bn' < 0  then -1  else bn'
   maxBn = maximum (bnd: bnsR)
   psL   = [(i, bnd) | i <- [1 .. ml']]
   psR   = filter ((>= 0) . snd) $ zip [(succ ml') .. m1] bnsR
   ps    = psL ++ psR
   inds  = concat [[[i, j] | j <- [0 .. d]] | (i, d) <- ps]
                                         -- variables (multiindices) the
                                         -- equations to be imposed for
   UPol _ a v dF = pp
   (zr, un)      = (zeroS a, unity a)
   vcp [i, j] [i', j'] =        -- variable comparison for U = F[uij..],
                                --                          first - by j
                         case compare j j' of EQ -> compare i i'
                                              x  -> x

   vcp' [i, j] [i', j'] = case compare i i' of EQ -> compare j j'
                                               x  -> x
   vterm = (vcp, "u", [(1, m1), (0, maxBn)])
   toU  = cToRPol vterm dF   -- F-> U= F[uij..] represented as RPol
   unU  = toU un             
   dU   = upRing unU Map.empty
   unTU = cToUPol v dU unU   -- 1 of U[t]
   zrTU = zeroS unTU
   toOverU f = ct unTU [(toU a, j) | (a, j) <- upolMons f]
                                                          -- F[t]-> U[t]
   t       = varP unU unTU                                -- t in U[t]
   tPowers = unTU: (pows t)  where  pows x = x: (pows (x*t))

   tUpol (i, d) =          -- u(i) = sum [u(i,j)*t^j| j<-[0..d]  of U[t]
              if d < 0  then zrTU  else  sum1 $ zipWith cPMul cs tPowers
                          where
                          cs = [varToRPol unU un [i, j] | j <- [0 .. d]]

   uVecL = [tUpol (i, bnd) | i <- [1 .. ml']]        -- [u_1..u_ml']
   uVecR = map tUpol $ zip [(succ ml') .. m1] bnsR   -- rest  u_i
   mH'   = mapmap toOverU mH
   uLB   = rowMatrMul uVecL mH'
                           -- vector over U[t], each component of ub has
                           -- linear polynomials from U  as coefficients
   uRB = map ((toOverU pp) *) uVecR
   ub  = zipWith (+) uLB uRB
   coefEquations = map fst . takeWhile ((> bnd) . snd) . upolMons
                                -- coefficients 
                                -- of deg_t > bnd  in a component of vec
   eqs  = concat $ map coefEquations ub
                                   -- Condition |ub| <= bnd:  a list of
                                   -- linear polynomials from U = R[uij]
   eqs' = reverse $ map canAssoc $ linRPolsToStaircase eqs
                                            -- to staircase r-pol system
   ---------------------------------------------------------------------
   -- given sorted by i,j  pairs = [(uij,aij)|..]  with the found 
   -- values  aij :: k,  rebuild  [u1..um1] :: [A]

   uValuesToA pairs = reverse $ 
                      pToVec m1 $ UPol (toOverA pairs) pp "x" Map.empty
      where
      toOverA []      = []
      toOverA (p: ps) =
                  -- [(uij, aij)| j<-[0..]]-> (sum [aij*t^j...], pred i)
        let (i: _, _   )  = p
            (ps',  ps'') = span ((== i) . head . fst) ps
            mons         = [(a, second v) | (v, a) <- (p: ps'), a /= zr]
            second (_: j: _) = j
        in  (ct pp mons, i-1): (toOverA ps'')
   ---------------------------------------------------------------------
 in
 if  vecLDeg 0 minVInH <= bnd  then  Just (minE ++ minVInH)
 else
 case solveLinRPolsStaircase eqs'
 of
      -- eqs'  is reversed staircase list of non-zero normed linear 
      -- polynomials. Non-zero solution is searched.
      -- Mind that  ker(B) = {0}  in the space of  [u1..um1].
 Nothing    -> Nothing
 Just pairs ->        -- pairs = [(uij,aij)|..]
    let
      ps      = sortBy (\ (u, _) (v, _) -> vcp' v u) pairs
      inds'   = map fst ps
      wrap ps = let (rowL, rowR) = genericSplitAt ml' $ uValuesToA ps
                    uBR          = zipWith (+) (rowMatrMul rowL mH)
                                               (map (pp *) rowR)
                in  Just (rowL ++ uBR)
     in
     if  any ((/= zr) . snd) ps  then  wrap ps
     else
     case  inds \\ inds'  of
                       ij: _ -> wrap [(ij, un)]  -- this uij is all free
                       _     -> Nothing


------------------------------------------------------------------------
linRPolsToStaircase :: Field k => [RPol k] -> [RPol k]
  -- LOCAL.
  -- Staircase form S of the sparse matrix M.
  -- M,S are represented as the lists of linear r-polynomials.
  -- Particular point:  as soon as a constant  c  appears, the 
  -- result is  [c].
  -- Example:  for  x > y > z,  [2*x + 3*y + 1,     [2*x + 3*y + 1,
  --                             4*x + z        -->  -6*y + z - 2
  --                            ]                   ]

linRPolsToStaircase fs =
  case
      span (not . pIsConst) $ filter (not . isZero) fs
  of
  (_,     f:_) -> [f]
  ([],    _  ) -> []
  (g: gs, _  ) -> red (g: gs)
    where
    vcp     = rpolVComp g
    red []  = []
    red [f] = [f]
    red fs  = 
      let
        v              = maxBy vcp$ map (fromJust . rpolHeadVar) fs
        (f: fs', fs'') = partition ((== v) . fromJust . rpolHeadVar) fs
        c            = lc f
        gs           = [g - (cPMul ((lc g)/c) f) | g <- fs']
      in
      case  span (not . pIsConst) $ filter (not . isZero) gs
      of
      (_,   g: _) -> [g]
      (gs', _   ) -> case red (gs' ++ fs'')
                     of
                     []  -> [f]
                     ss  -> case  span (not . pIsConst) ss  
                            of
                            (_, s:_) -> [s]
                            _        -> f: ss



------------------------------------------------------------------------
solveLinRPolsStaircase :: Field k => [RPol k] -> Maybe [(RPolVar, k)]
  -- LOCAL.
  -- fs  is the reversed staircase list of non-zero normed linear 
  -- r-polynomials.
  -- Returns  Nothing,          if no solution exists,
  --          Just [(v1,a1)..]  otherwise,  if possible, non-zero 
  --                            solution is chosen.
  -- vi  not listed in the solution pairs have arbitrary values. 
  -- Method:
  -- For the first equation f,  assign the values  ai  to the free
  --   variables  vi  (the ones contained in  pTail f),
  --   express the head variable  v  via  ai,
  --   substitute these values into other equations fs ...

solveLinRPolsStaircase []      = Just []
solveLinRPolsStaircase (f: fs) = 
                 if pIsConst f then  Nothing  else  Just $ solve (f: fs)
  where
  solve []      = [] 
  solve (f: fs) = -- here fs does not contain constants
    let
      (un, tl, v) = (lc f, pTail f, fromJust $ rpolHeadVar f)
      (zr, u:vs)  = (zeroS un, rpolVars 'l' tl)
      fsL         = genLength (f: fs)
      assigns = case rpolRepr tl
                of
                CRP a             -> [(v, -a)]
                NRP _ _ (CRP b) _ -> 
                         (if a == zr then (v, -b): (u, un): (zip vs zrs)
                          else            (v, -a): (zip (u: vs) zrs)
                         )
                         where {a = pFreeCoef tl;  zrs = repeat zr}
    in
    if  un == unity un  then
              assigns ++ (solve (map (substValsInRPol 'l' assigns) fs))
    else
    error $ concat 
    ["\nsolveLinRPolsStaircase fs\n- probably, called from  \
     \factorOverFinField_2 q:\n\nnot normed r-polynomial met in the \
     \system\n- why ?\nlength fs =  ", shows fsL $  
     showsWithDom 1 f "head fs" "" ".\n"]
