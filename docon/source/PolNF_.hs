------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------




module PolNF_   -- Reduction to Groebner Normal Form of polynomial.
                -- All needed from here is  reexported by  GBasis.

(polNF, polNF_v, polNF_e, polNF_ev, test_polNF, underPPs, 
 
 coefNF, makeModes   -- local
)
where
import Data.Maybe (isJust)
import Data.List  (transpose, partition)
import Prelude hiding (minimum, maximum)

import DPrelude (Length(..), -- class
                 Natural, PropValue(..), InfUnn(..), Z, 
                            ct, tuple31, minimum, maximum, showsWithDom)
import Categs     (Dom(..))
import SetGroup   (Set(..), MulSemigroup(..), zeroS, isZero)
import RingModule (EuclideanRing(..), LinSolvRing(..), GCDRing(..), 
                                                          isCEucRing)
import VecMatr (Vector(..), vecRepr)
import PP_     (PowerProduct, ppDivides)
import UPol_   (PolLike(..), lc)
import Pol_    (Pol(..), polMons, mPolMul)
import Pol__   (PVecP, sPol)
import EPol0_  (EPol(..), epolMons, eLm, eLpp)
import EPol1_  (EPVecP, mEPolMul)






------------------------------------------------------------------------
polNF :: 
       EuclideanRing a => String -> [Pol a] -> Pol a -> (Pol a, [Pol a])
                          -- mode   gs         f        rem     qs
{-
Normal form of polynomial over a Euclidean ring  a.
Also the *quotient vector*  qs is accumulated:
                                  f = scalarProduct(qs,gs) + remainder
The following properties hold.
If  gs  is a weak Groebner basis [Mo], then
             (fst (polNF anyMode gs f)) ==0  <==>  f <- I = Ideal(gs)
             and
             if also `a' is a  c-Euclidean ring, then
                       fst .(polNF "c" gs)  is a canonical map modulo I.

mode = tailMode ++ cMode,   the order is immaterial, 
                            also "c"  is equivalent to "cr", "rc".

tailMode =    ""    means to reduce the head monomials only,
            | "r"         to reduce the tail too.
cMode    is the mode for the coefficient reduction in moduloBasis;
         it is processed only when the current  lm(f)  is not the 
         multiple of any lm(g).  (moduloBasis m bs a)  is applied 
         for  bs = [lc(g)| lpp(g) divides lpp(f)]   with m = cMode.
Method
------
It contains the local procedure  nf  for  tailMode = "",  which 
reduces only the head monomial while possible.  tailMode = "r"  is
computed by the recursive application of  nf  to the tail. 
Now let us describe  nf.

First  gi  are paired with the factors qi initiated with 0. 
This makes  gqs.
In the end,   f = r + g1*q1+...+gn*qn,    qi  are extracted from the
pairs, and (r,qs) is returned.
For the current  monF = (a,ppF) = lm(f),  appendPPQuot  extends each
(g,q)  of  gqs  to  gqt = ((g,q),qt),  qt = Nothing | Just d,
qt==(Just _)  means that in the given gqt  g  is a divisor,  that is
lpp(g) divides ppF.   gqqs = appendPPQuot gqs.
The divisors  gqqDs  are copied out from  gqqs.
bs = [lc(gi) | gi from gqqDs].

(a',ds) = coefNF cMode bs a    
    reduces  a  to  a'  accumulating the quotients  ds.
    And as the ring is Euclidean, coefNF acts like the extended gcd,
    applying  divRem _ a gcd(bs)  in the end.

Each di multiplies the corresponding power product  pi'= ppF-lpp(gi)
and sums it to polynomial  qi:  qi' = qi+di*pi'.
The new head monomial for  f  is  (a',ppF),  if  a' /= zero;  
the new tail is  pTail(f) - sum(di*pi'*polTail(gi) ...).

gqs' = merge q's gqqs    overwrites  qi  with  qi'  in  the  divisor 
items in  gqqs.  This finishes the cycle of the  lm(f)  reduction.

makeModes, merge, coefNF   are the LOCAL functions in this module,
they are common to  polNF,polNF_e. 
See them below the polNF script.

Optimizations.
*
coefNF  first applies  (r,ds) = nfs bs a.
Then, if  r  is not zero, applies moduloBasis.
nfs  searches only the precise divisor.  This saves much in the 
case when some  lc(g)  divides  lc(f),  g  from  gqqDs /= []. 
This always holds in the field case.
*
nfs  does not fill the tail zeroes in  ds.  And `merge' and some
other functions take in account that  ds,q's  may be shorter than 
gqqDs  and so on.
-}


polNF mode gs f = 
  let
    (zr, zeroPol)     = (zeroS $ sample f, zeroS f)
    gqs               = [(g, zeroPol) | g <- gs]
    (tailMode, cMode) = makeModes mode
    --------------------------------------------------------------------
    -- append  pp-lpp(g) to (g,q):  pp -> (g, q) -> ((g, q), qt)  

    appendPPQuot pp gq@(g, _) =  
      if
        isZero g  then  (gq, Nothing)
      else
      let ppG = lpp g  
      in  
      if  ppDivides ppG pp  then (gq, Just (pp - ppG))
      else                       (gq, Nothing        )
    --------------------------------------------------------------------
    nf []  f = ([], f)          -- reduce f while possible, by head only
    nf gqs f =
      if
        isZero f  then (gqs,f)
      else 
      let (a, ppF) = lm f
          gqqs     = map (appendPPQuot ppF) gqs
          gqqDs    = filter (isJust . snd)  gqqs -- lpp-divisors for ppF
          bs       = map (lc . fst . fst) gqqDs
          (a', ds) = coefNF cMode bs a
          monF'    = (a', ppF)

          q's = zipWith dTo_q ds gqqDs           -- accumulate quotients 
                where                            -- each divisor gi 
                dTo_q d ((_, q), Just p') =  
                                     if d == zr then  q
                                     else             q + (ct f (d, p'))

          newTail = foldl (-) (pTail f) $ zipWith tailProduct ds gqqDs
                        where         
                        tailProduct d ((g, _), Just p') =
                             if  
                                d == zr  then  zeroPol
                             else              mPolMul (d, p') $ pTail g
          gqs' = merge q's gqqs
      in
      if  a' == zr  then  nf gqs' newTail  
      else                (gqs', ct f (monF': (polMons newTail)))
    --------------------------------------------------------------------
    processWithTail gqs f = 
      let 
        (gqs' , r' ) = nf gqs f  
        (gqs'', r'') = processWithTail gqs' $ pTail r'
      in
      if  isZero r' || not tailMode  then  (gqs', r')
      else                        (gqs'', ct f ((lm r'): (polMons r'')))
    --------------------------------------------------------------------
    (gqs', r) = processWithTail gqs f 
  in
  (r, map snd gqs')




------------------------------------------------------------------------
-- makeModes, merge, coefNF  are the LOCAL functions common to
-- polNF, polNF_e.
-- See the header comments for  polNF.

makeModes mode = 
    case (genLength mode <= 2, elem 'c' mode)  
    of
    (True, True) -> (True,          True )    -- (rMode,cMode)
    (True, _   ) -> (elem 'r' mode, False)
    _            ->
         error $ concat ["\npolNF(_e) mode gs f:  mode must be \
                         \tailMode ++ cMode,\ntailMode = \"\" | \"r\", \
                         \cMode = \"\" | \"c\" \n"]

------------------------------------------------------------------------
merge :: Set q => [q] -> [((g, q), Maybe PowerProduct)] -> [(g, q)] 
                                                     -- LOCAL.
                                                     -- update quotients
merge []       pairs                = map fst pairs
merge (q': qs) (((g, q), x): pairs) = 
                              case x  
                              of  
                              Nothing -> (g, q) : (merge (q': qs) pairs)
                              _       -> (g, q'): (merge qs       pairs)
merge (q': _)  _  = 
              error ("\npolNF(_e) ... (PolNF_.merge (q: _) [])    - ?\n"
                     ++ (showsWithDom 1 q' "q" "" "\n"))

------------------------------------------------------------------------
coefNF :: EuclideanRing a => Bool -> [a] -> a -> (a, [a])   
coefNF                       cMode   bs     a = 
  let zr  = zeroS a
      mbm = if cMode then "c" else ""

      nfs []      a = (a, [])
      nfs (b: bs) a = case divide_m a b  
                      of
                      Just d -> (zr, [d])
                      _      -> (a', zr: ds) where (a', ds) = nfs bs a
      (r, ds) = nfs bs a    
  in  
  if  r == zr  then  (r, ds)  else  moduloBasis mbm bs a    

{-# specialize coefNF :: Bool -> [Z] -> Z -> (Z, [Z]) #-}


-----------------------------------------------------------------------
polNF_v :: EuclideanRing a => String -> [PVecP a] -> PVecP a -> PVecP a

-- Normal form for the VecPol -s.
-- Differs from  polNF  in that the polynomial reduction is extended 
-- (with the same coefficients) to the vector parts.

polNF_v mode gvs (f, v0) =  
  let                             -- redV u qs vs  ->  u-q1*v1-..-qn*vn
    redV u []      []      = u         
    redV u (q: qs) (v: vs) = redV (zipWith (\ x y -> x -q*y) u v) qs vs
    (r, qs)                = polNF mode (map fst gvs) f 
                                                -- f-q1*g1-..-qn*gn = r
  in  
  (r, redV v0 qs $ map snd gvs)


------------------------------------------------------------------------
polNF_e :: EuclideanRing a => 
                       String -> [EPol a] -> EPol a -> (EPol a, [Pol a])

-- Differs from  polNF  in that the power products are extended and in 
-- that the condition  "lpp(gi) divides lpp (f)"  is enforced by adding
-- "and  eLpp(gi), eLpp(f)  have the same coordinate No".

polNF_e  mode  gs  f@(EPol _ _ pol) = 
  let
    (zr, zeroEPol)    = (zeroS $ sample pol, zeroS f)
    zeroPol           = zeroS pol
    gqs               = [(g, zeroPol) | g <- gs]
    (tailMode, cMode) = makeModes mode
    --------------------------------------------------------------------
    appendPPQuot (i, pp) gq@(g, _) =  
      if
        isZero g  then (gq, Nothing)
      else
      let (j, ppG) = eLpp g
      in   
      if  i /= j || not (ppDivides ppG pp)  then  (gq, Nothing)
      else                                        (gq, Just (pp - ppG))
    --------------------------------------------------------------------
    nf []  f = ([], f)                    -- nf reduces by the head only
    nf gqs f =
      if  isZero f  then (gqs, f)
      else 
      let (a, eppF) = eLm f
          gqqs      = map (appendPPQuot eppF) gqs
          gqqDs     = filter (isJust . snd) gqqs  
          bs        = map (lc . fst . fst) gqqDs
          (a', ds)  = coefNF cMode bs a    
          monF'     = (a', eppF)

          q's = zipWith dTo_q ds gqqDs
                where                      -- accumulate quotient for gi
                dTo_q  d ((_, q), Just p') =  
                                  if  d == zr then  q
                                  else              q + (ct pol (d, p'))

          newTail = foldl (-) (pTail f) $ zipWith tailProduct ds gqqDs
                    where         
                    tailProduct d ((g, _), Just p') =
                            if  
                               d == zr  then  zeroEPol
                            else              mEPolMul (d, p') (pTail g)
          gqs' = merge q's gqqs
      in
      if  a' == zr  then  nf gqs' newTail  
      else                (gqs', ct f (monF': (epolMons newTail)))
    --------------------------------------------------------------------
    processWithTail gqs f = 
      let 
         (gqs', r')   = nf gqs f 
         lM           = eLm r'
         (gqs'', r'') = processWithTail gqs' $ pTail r'
      in
      if  isZero r' || not tailMode  then  (gqs',r')
      else                            (gqs'', ct f (lM: (epolMons r'')))
    --------------------------------------------------------------------
    (gqs', r) = processWithTail gqs f
  in
  (r, map snd gqs')





------------------------------------------------------------------------
polNF_ev :: 
         EuclideanRing a => String -> [EPVecP a] -> EPVecP a -> EPVecP a

polNF_ev mode gvs (f, v0) =    -- similar to  polNF_v
  let
    redV u []      []      = u         
    redV u (q: qs) (v: vs) = redV (zipWith (\ x y -> x - q*y) u v) qs vs
    (r, qs) = polNF_e mode (map fst gvs) f 
  in 
  (r, redV v0 qs $ map snd gvs)



test_polNF :: (EuclideanRing a, GCDRing a) =>  Bool -> [Pol a] -> String
                                             -- isG    fs
-- Testing  sPol, polNF.
-- isG  means  "fs is a weak Groebner basis".
-- Each s-polynomial s(f,g),  f,g <- fs,  is reduced to
-- sR(f,g) = polNF _ fs s(f,g).  
-- Then,  isG = True <==> all sR(f,g) = 0 

test_polNF isG [] = error ("\ntest_polNF " ++ (shows isG " [].\n")) 
test_polNF isG fs = 
  let 
    f         = head fs
    (aDom,zr) = (dom f, zeroS $ sample f)
    gColumn   = transpose [fs]
    sp f g    = tuple31 $ sPol f g

    pairs [_]     = []
    pairs (x: xs) = [(x, y)| y <- xs] ++ (pairs xs)

    sPols    = [sp f g | (f, g) <- pairs fs]
    reductsH = map (fst . polNF ""  fs) sPols
    reductsC = map (fst . polNF "c" fs) sPols
    --------------------------------------------------------------------
    result = 
      case (isG, all isZero reductsH, all isZero reductsC) 
      of
      (True,  True,  True ) -> 
                        "SUCCESS:\nfs  declared a weak Groebner basis,\
                        \ and all s-polynomials\n have reduced to zero."
      (True,  _,     _    ) ->
                      "ERROR:\nfs  declared a weak Groebner basis, but \
                      \some of s-polynomials\ndo not reduce to zero.\n\
                                            \Test the \"c\" mode too.\n"
      (False, False, False) ->
               "SUCCESS:\nfs  is declared as NOT a weak Groebner basis,\
               \ and some\nof s-polynomials do not reduce to zero.\n"
      _                     ->
                "ERROR:\nfs  is declared as NOT a weak Groebner basis, \
                \but all of s-polynomials have reduced to zero.\n\
                \Test the \"c\" mode too.\n"
    --------------------------------------------------------------------
  in
  case  isCEucRing $ snd $ baseEucRing zr aDom
  of
  Yes -> "gs =\n" ++ (shows gColumn ("\n\n\n" ++ result))
  _   -> error $ concat 
         ["\ntest_polNF ", shows isG " fs,  length fs =  ", 
          shows (genLength fs) $ showsWithDom 1 f "head  fs" ""
          "\nA c-Euclidean coefficient ring needed,\n"]


------------------------------------------------------------------------
underPPs :: [PowerProduct] -> (InfUnn Natural, [PowerProduct])

-- A power product  p  is called an "under" power product with 
-- respect to the power product list pps  if none of pps  divides p.
-- "Under" monomials are useful in computation in the residue rings
-- of the polynomial ring. This is because for the coefficient field 
-- k,  P = k[x1..xn],  gs  a Groebner basis,  pps = map lpp gs,  
-- under-s  form a linear basis of  P/Ideal(gs)  over  k.
-- Trivial Lemma:
-- the set of "under" power products  is finite  if and only if for
-- any  xi <- vars,  1 <= i <= n,   pps  contains  p = xi^k, 
-- k > 0   - that is  p = Vec [0..0,k,0..0].
--------------------------------------------------------------------
-- underPPs pps  
-- yields the  list (and a number) of the  "under" power  products 
-- for a given list of any power products  pps.
-- 
-- Returns   (Infinity, [])  for the infinite list,
--           (Fin 0,    [])  for the empty list.
-- Examples:
--   underPPs [Vec [0,3], Vec [1,2]]            --> (Infinity, [])
--   underPPs [Vec [0,3], Vec [1,2], Vec [2,0]] -->
--              (Fin 5,
--               [Vec [0,0],Vec [0,1],Vec [0,2],Vec [1,0],Vec [1,1]])
-- MIND: 
-- the very list may be sometimes stupidly long, hard to print,  and 
-- so on. For example,  for  pps = [x^10,y^10,z^10,u^10],
-- underPPs pps 
-- yields (10000, pps'),  pps' = [[0,0,0,0],[0,0,0,1],...].
--
-- But if you use only the *number*, like say, in
--                                   let (n,_) = underPPs pps  in...
-- then the evaluation is as cheap as possible.

underPPs pps = 
  if  
     any isZero pps  then (Fin 0, []          )
  else                    (n,     map Vec pps')
  where
  (n, pps')    = underpps $ map vecRepr pps
  underpps pps = 
    (case partition isX1monic pps                   -- reducing to  upps
     of
     ([],       _   ) -> (Infinity, [])             -- x1 is not bounded
     (x1monics, pps') -> let dim   = genLength $ head x1monics
                             i     = minimum $ map head x1monics
                             pps'' = filter ((< i) . head) pps'
                         in  upps i dim pps''
    )
    where
    -- Here we call a
    --  monic pp the one of kind  xi^k,  k>0  <-->[0..0,k,0..0],
    --  x1-monic any monic pp  with  (head pp) > 0.

    isX1monic []      = False
    isX1monic (j: js) = j /= 0  &&  all (== 0) js

                                   -- Cartesian product pps x [i..j]
    cartProduct pps i j = concat (map (prependToAll pps) [i .. j])
                                      where
                                      prependToAll pps i = map (i :) pps
    divides js ks = all (\ (j, k) -> j <= k) $ zip js ks

    reduceMutually []        = []
    reduceMutually (pp: pps) = 
               let pps' = reduceMutually (filter (not . divides pp) pps)
               in
               if  any (\ q -> divides q pp) pps'  then  pps' 
               else                                      pp: pps'
  
    -- upps i dim pps   yields the "under" pp-s for (x1^i :pps).
    -- Here  pps  does not contain x1-monics,  i > 0  and  
    --                                                  deg(pps,x1) < i.
    upps i 1   _   = (Fin i,    [[j] | j <- [0 .. (pred i)]])
    upps _ _   []  = (Infinity, [] )                   -- x2 not bounded
    upps i dim pps =
      let
        j    = maximum $ map head pps
        ppsS = filter ((/= j) . head) pps
                 -- denote  (ppsM, ppsS) = partition ((== j) . head) pps
      in
      case (ppsS, j > 0)
      of
      ([], True) -> (Infinity, [])        -- deg(*,x1) > 0  on pps
                                          -- => x2 is not bounded
      ([], _   ) ->                       -- deg(*,x1) = 0  on pps, 
           case underpps $ map tail pps   -- the dimension is reduced
           of
           (Infinity, _   ) -> (Infinity, [])
           (Fin n0,   pps0) -> (Fin (n0*i), cartProduct pps0 0 (pred i))
      _ -> 
        -- Here the maximal i1 pp-s ppsM and the rests (ppsS) are both 
        -- non-empty. 
        -- First list the under-s with  i1 < j,  ppsM  cannot divide any
        -- of these pp.  Then list the under-s  ppjs  given by  i1 = j  
        -- projecting them to  i1 = 0,  and multiply it by the segment 
        -- [j..(i-1)].
        -- Any  p  from ppsS divides q = (j:_)  from  ppjs  if and only 
        -- if  tail(p) divides tail(q).  Hence we have to process all 
        --                         the tails of pps when computing ppjs.
        case upps j dim ppsS  
        of
        (Infinity, _     ) -> (Infinity, [])
        (Fin nsu,  ppsS_u) -> 
                   case  underpps $ reduceMutually $ map tail pps
                   of
                   (Infinity, _   ) -> (Infinity, [])
                   (Fin nj,   ppjs) -> 
                               (Fin (nsu + nj*(i - j)),
                                ppsS_u ++ (cartProduct ppjs j (pred i)))
