-- DoCon-2.04  Demonstration, test, benchmark.


-- Polynomial arithmetics and gcd.
-- * Testing the isomorphism between 
--                           P = Z[z,y,x]  and  UU[z],  UU = Z[x][y],
-- * correctness of arithmetic in P, UU[z],
-- * comparing P, UU[z] for the arithmetic performance.
-- * GCD in P.
-- See statistics in  Manual,  Section on performance comparison.



module T_polArit  (t_polarit_)
where
import qualified Data.Map as Map (empty)

import DPrelude   (Natural, ct, smParse, alteredSum)
import SetGroup   (power)
import RingModule (upGCDRing, gcd_test)
import Z          (dZ)
import VecMatr    (vecRepr)
import Pol        (UPol(..), Pol(..), lexPPO, upolMons, polMons, cToPol,
                                      cToUPol, fromUPol, fromHeadVarPol)
type R  = Integer
type P  = Pol  R    -- for  P  = R[z,y,x]
type U  = UPol R    --      U  = Z[x]
type UU = UPol U    --      UU = U[y]

t_polarit_ = 

 (test10,                 -- (^n) correctness in P, UU[z]
  map (gcdT 1) [1 .. 3],  -- gcd correctness in P   
  powTest,                -- for f^n benchmarking, say, 
                          --                       tuple32 $ powTest 18
  gcdT,                   -- for gcd (d^n*f1^m) (d^n*f2^m) benchmarking,
                          -- for example:  last $ snd $ gcdT 2 8
  (f*f, unx, uny, [fz, fz*fz])   -- simplest "visual" test
 )
 where
 (dR, [o1, o2, o3]) = (dZ, map lexPPO [1, 2, 3])
 vars2 = ["y", "x"]
 vars  = "z": vars2
 unp   = cToPol o3 vars  dR 1   :: P
 un2   = cToPol o2 vars2 dR 1   -- of R[y,x]
 d2    = upGCDRing un2 Map.empty      -- description of R[y,x]
 unx   = cToUPol   "x"   dR 1   :: U -- = R[x]
 unx1  = cToPol o1 ["x"] dR 1   -- of R[x] <--> Pol R
 dX    = upGCDRing unx  Map.empty     
 dX1   = upGCDRing unx1 Map.empty     
 uny   = cToUPol "y" dX  unx    :: UU
 uny'  = cToUPol "y" dX1 unx1    
 dY    = upGCDRing uny Map.empty          
 unz   = cToUPol "z" dY uny    :: UPol UU
 un2z  = cToUPol "z" d2 un2    -- of R[y,x][z]

 str   = " 2*y*z + z + y*x + 3*y + 1 "
 f     = smParse unp str  
 fz    = smParse unz str
 -----------------------------------------------------------------------
                -- prepare the conversion UU[z] -> R[y,x][z] -> R[z,y,x]

 toDY' = ct uny' . (map (\ (a, e)->(fromUPol a, e))) . upolMons
                       -- R[x][y] -> R[x]'[y],  R[x]' represented as Pol
 toOverD2 = 
           ct un2z . (map (\ (a, e) -> (fromHeadVarPol (toDY' a), e))) . 
           upolMons
                                                   -- UU[z] -> R[y,x][z]
 toP = fromHeadVarPol . toOverD2
             -- R[x][y][z] -> R[z,y,x],
             -- It starts with mapping of coefficients from UU to R[y,x]
 -----------------------------------------------------------------------
 powTest :: Natural -> (Bool, ([R], [[Integer]]), (P, UPol UU))
 powTest n =  (pFromHTest, (cs3, pp3), (fp, fzp))
                    -- test coefficients and power products in f^n, fz^n
        where
        (fp, fzp)  =  (power f n, power fz n)  
        pFromHTest =  fp == (toP fzp) 
                     -- has to be True, because  (toP f) == fz,
                     -- (fp, fzp) == (f^n, fz^n)  and toP is isomorphism
        (cs, pps) = unzip $ polMons fp
        cs3       =             [head cs , last cs , alteredSum cs ] 
        pp3       = map vecRepr [head pps, last pps, alteredSum pps]

 test10 = let (fromH, (cs, pps), _) = powTest 10     -- for test only
          in
          (fromH, cs == [1024, 1, 6897832] &&
                  pps == [[10,10,0], [0,0,0], [3,33,-6]])
           
 -----------------------------------------------------------------------
                                          -- testing gcd in P = R[z,y,x]
 d        = smParse unp "(2*z + 3*y + 4*x)*(z*y*x^2 + y^3 + 1)"
 f1       = smParse unp "z + y + x    "
 f2       = smParse unp "z - y + x + 2"
 gcdT n m = gcd_test 1 (power d n) (power f1 m) (power f2 m)
 