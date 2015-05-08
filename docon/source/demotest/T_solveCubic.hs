------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2014
------------------------------------------------------------------------
------------------------------------------------------------------------



import qualified Data.Map as Map (empty)
import Data.List (nub)

import DPrelude   
import RingModule 
import Fraction (Fraction(..))
import Pol 
import SolveCubic (Kr, E3, SolveCubic(..), GBasisOrNot(..), solveCubic)



-- ***************************************************************************
type Q  = Fraction Integer 
type Qr = Kr Q             -- for Q(r) = Q(rt(-3))
type A  = UPol Q  


main = putStr $ concat
       [
        "f =  ",           shows f "\n\n", 
        "i^2 = ",          shows (i^2) ",  ", 
        "s^2 = ",          shows (s^2) ",  ", 
        "eta^3 = ",        shows (eta^3) ",   ",
        "eta^2+eta+1 = ",  shows (eta^2 + eta + unQr) "\n\n",
 
        "f_can =  ",     shows f_can "\n", 
        "discr = ",      shows discr "\n",
        "carEqs =\n",    showsn 1 carEqs "\n",
        "gs =\n",        showsn 1 gs "\n\n",
        -- "roots_nub =\n", showsn 1 roots_nub "\n\n",
        "roots =\n",     showsn 1 rts "\n\n",
        "f_atRoots = ",  shows f_atRoots "\n",
        "vtTest = ",     shows vtTest "\n"
       ]
  where
  un  = 1:/1  :: Q
  dK  = upField un Map.empty
  unA = cToUPol "x" dK un
  x   = varP un unA  

  [n1, n2, n4] = map (fromi unA) [1, 2, 4]

  f = -- x*(x^2 - n1)
      -- x*(x - n1)*(x - n2)
      x^3 - n1*x + n1   
      -- x^2*(x - n1)     

  [a2, a1, a0] = map (pCoef f) [[2], [1], [0]]  
                                -- coefficients of f besides the leading one

  solution = solveCubic GBasis "" a2 a1 a0 dK   :: SolveCubic Q

  (i, s, s3, eta) = i_ss_eta solution  :: (Qr, Qr, Qr, Qr)

  f_can  = canonicPol      solution    :: UPol Qr
  discr  = discrim         solution    :: Qr
  carEqs = cardanoEqs      solution    :: [Pol Qr]
  gs     = cardanoGroebner solution    :: [Pol Qr]
  rts    = roots           solution    :: [E3 Q]
  toQr   = kToKr           solution    :: Q -> Qr
  qQrToE = k_rToExt        solution    :: Qr -> E3 Q

  kToE = qQrToE . toQr

  [x1, x2, x3] = rts 
  roots_nub    = nub rts

  unQr = fromi i 1                   :: Qr
  unE  = fromi x1 1                  :: E3 Q
  dE   = upLinSolvRing unE Map.empty
 
  unPE = cToUPol "t" dE unE  :: UPol (E3 Q)
  t    = varP unE unPE       

  [a2', a1', a0'] = map (ctr unPE . kToE) [a2, a1, a0]
  fE              = t^3 + a2'*t^2 + a1'*t + a0'

  f_atRoots = [pValue fE [r] | r <- rts]   -- must be [0,0,0]

  elemSyms = [x1 + x2 + x3,           -- testing Viete relations
              x1*x2 + x1*x3 + x2*x3,
              x1*x2*x3
             ]                            
  vtCheck = map kToE [- a2, a1, - a0]
  vtTest  = elemSyms == vtCheck   


{-
gs = [v^2 + (1/2)*u*r*d, 
      u*v - 3, 
      u^2 - (1/2)*v*r*d
     ]
u^2 + v^2 = 0,   v = +-u
1) v = u
   u^2 - urd/2
   x1 = (u + v)/3 = u*2/3 = 2*rt(3)/3   no such root!
   u = rt(3)

2) v = -u
   x1 = (u+v)/3 =  0   OK.

---------
x2 =  (-1/6)*u*r - (1/6)*u + (1/6)*v*r - (1/6)*v
   =  (1/6)*(-u*r - u + v*r - v)
   =  (1/6)*(r*(-u + v) - u - v)

-}
