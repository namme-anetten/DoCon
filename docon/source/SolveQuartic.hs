{-
Solving a quartic equation   f =  x^4 + a*x^3 + b*x^2 + c*x + d = 0 
having _real_ coefficients.

Ferraris's method.


-- Discrimminant --------------------------------------------------------

Discriminant = Delta =
  256*d^3 - 192*a*c*d^2 - 128*b^2*d^2 + 144*a^2*b*c^2*d - 27*c^4 
  + 144*a^2*b*d^2 - 6*a^2*c^2*d - 80*a*b^2*c*d + 18*a*b*c^3 + 16*b^4*d 
  - 4*b^3*c^2 - 27*a^4*d^2 + 18*a^3*b*c*d - 4*a^3*c^3 - 4*a^2*b^3*d 
  + a^2*b^2*c^2 

P =  8*b - 3*a^2

Delta_0 =  b^2 - 3*a*c + 12*d         -- is 0 if  f  has a triple root

D = 64*d - 16*b^2 + 16*a^2*b - 16*a*c - 3 a^4
                                      -- is 0 if the f has  two double roots


The possible cases for the nature of the roots are as follows:

* If Delta < 0  then f has  two real roots and two complex conjugate roots.
* If Delta > 0  then the roots are either all real or all complex.
  o If P < 0 and D < 0  then all four roots are real and distinct.
  o If P > 0 or D > 0   then there are two pairs of complex conjugate roots.
    
* If Delta = 0  then either f has a multiple root, or it is the square of a 
                quadratic polynomial. 
  Here are the different cases that can occur:
  o If P < 0 and D < 0  and \Delta_0 /= 0,  
                        there is a real double root and two real simple roots.
  o If (P > 0 and D ≠ 0) or D > 0,  
                  there is a real double root and two complex conjugate roots.
  o If Delta_0 = 0 and D /= 0,  
                           there is a triple root and a simple root, all real.
  o If D = 0, then:
              If P < 0,  there are two real double roots.
              If P > 0,  there are two complex conjugate double roots.
              If Delta_0 = 0,  all four roots are equal to  -a/4

There are some cases that do not seem to be covered, but they can not occur. 
For example  Delta > 0, P = 0 and D <= 0 is not one of the cases. 
However  if Delta > 0 and P = 0 then D > 0 so this combination is not 
possible.

-- Viete relations ------------------------------------------------------

  x1 + x2 + x3 + x4                              = -a
  x1*x2 + x1*x3 + x1*x4 + x2*x3 + x2*x4 + x3*x4  = b
  x1*x2*x3 + x1*x2*x4 + x1*x3*x4 + x2*x3*x4      = -c
  x1*x2*x3*x4                                    = d


-- Ferrari's method  ------------------------------------------------------

a1 = a*c - 4*d
a0 = 4*b*d - a^2*d - c^2

Resolvent = res =   y^3 - b*y^2 + a1*y + a0.

Find  y1  a real  (any?)  solution to  res;
and put
        r1 = rt(a^2 - 4*b + 4*y1),
        r2 = rt(y1^2 - 4*d),
      
        p = a  +- r4,
        q = y1 -+ r2.
Then
        x =  1/4 * (- p +- rt(p^2 - 8*q))

are the roots to  f. 
That is:

  p1 = a + r1
  p2 = a - r1
  q1 = y1 - r2
  q2 = y1 + r2

  r3 = rt(p1^2 - 8*q1)
  r4 = rt(p2^2 - 8*q2)

  x1 = (- p1 + r3)/4    = (- a - r1 + r3) /4
  x2 = (- p1 - r3)/4    = (- a - r1 - r3) /4
  x3 = (- p2 + r4)/4    = (- a + r1 + r4) /4
  x4 = (- p2 - r4)/4    = (- a + r1 - r4) /4


-- Testing -------------------------------------------------------------

f =  x^4 - 1
a = b = c = 0,  d = -1.

resol =  (y^3 + 4*y)  =  y*(y^2 + 4)    -- y1 =  ((1/3)*u + (1/3)*v)

1) Try  y1 = 0.

r1 = 0,   r2 = rt(4) = 2,  p1 = p2 = 0,   q1 = -2,  q2 = 2.
r3 = rt(-8*-2) = 4
r4 = rt(-8*2)  = 4*i 

x1 = r3/4 = 1
x2 = -1
x3 = r4/4 = i
x4 = -i                OK.

2) Try  y1 = 2i.

r1 = rt(4*2i) = rt(8i),  r2 = rt(y1^2 + 4) = 0.
p1 = rt(8i)
p2 = -rt(8i)
q1 = 2i 
q2 = 2i

r3 = rt(p1^2 - 8*q1) =  rt(8i - 8*2i) = rt(-8i)
r4 = rt(p1^2 - 8*q2) =  rt(-8i)

x1 = (- p1 + r3)/4 = 
     (-rt(8i) + rt(-8i)) /4 =  
     (-rt(2i) + rt(-2i)) /2 =  
     (-rt(i) + rt(-i)) * rt(2)/2 =  
     ( -rt(2)/2 - i*rt(2)/2  + (-rt(2)/2 + i*rt(2)/2) ) * rt(2)/2 = 
     = -1

x2 = (- p1 - r3)/4 = 
     (-rt(8i) - rt(-8i)) /4 =  
     (-rt(2i) - rt(-2i)) /2 =  
     (-rt(i)  - rt(-i)) * rt(2)/2 =  
     ( -rt(2)/2 - i*rt(2)/2  - (-rt(2)/2 + i*rt(2)/2) ) * rt(2)/2 = 
     -i*rt(2)*rt(2)/2 = 
     -i  

x3 = (- p2 + r4) /4 = 
     (rt(8i) + rt(-8i)) /4 =  (rt(2i) + rt(-2i)) /2 =  
     (rt(i) + rt(-i)) *rt(2)/2 =
     i 

x4 = (- p2 - r4) /4 = 
     (rt(8i) - rt(-8i)) /4 =  (rt(2i) - rt(-2i)) /2 =  
     (rt(i) - rt(-i)) *rt(2)/2 =
     1

OK.
In the program:
f(xi)  and  equationsForF4  contain many r2.

But why does not it derive  r2 = 0  ?


x1    =  (r3 - r1)/4  
f(x1) =  (-1/8)*r3*r1*r2 + (1/6)*r2*(u + v)     Is this 0 ?

  ( (-1/8)*r3*r1*r2 + (1/6)*r2*(u + v) ) *
  (  (1/8)*r3*r1*r2 + (1/6)*r2*(u + v) ) 
  = 
  (1/36)*r2^2*(u + v)^2  - (1/64)*r3^2*r1^2*r2^2 
  = 
  r2^2 * ((1/36)*(u + v)^2  - (1/64)*r3^2*r1^2)
  = 
  


---------------------------------------------------------
f =  (x - 1)^4  = x^4  -4*x^3 + 6*x^2 -4*x + 1  
                       a        b     c      d
resol =  y^3 - 6*y^2 + 12*y - 8
y1 = 2
d = 0,   v = 0,  u = 0,  r1 =0,  r2^2 =  y1^2 - 4 =  0

p1 = -4,  p2 = -4,  q1 = 2,  q2 = 2

r3 = rt(16 - 8*q1) = 0 
r4 = rt(16 - 8*q2) = 0     x1 = (4 + 0)/4 =  1    ...  OK


---------------------------------------------------------
f =  x^4 + 2*x^2 - 1/3
resol =  y^3 - 2*y^2 + (4/3)*y - (8/3)


-}



-- ***************************************************************************
{-# LANGUAGE ScopedTypeVariables, MonoLocalBinds #-}

module SolveQuartic (SolveQuartic(..), Kr, F4, solveQuartic)
where
import qualified Data.Map as Map (insert)
import DPrelude
import Categs (CategoryName(..), Dom(..), Domain1(..), Domains1, Ideal(..))
import SetGroup (unity, inv) 
import RingModule
import Pol
import Pol_       (polPPComp)
import GBasis     (gBasisWithRadicals)
import Residue    (Residue(..), ResidueI(..))
import SolveCubic (SolveCubic(..), GBasisOrNot(..), Kr, E3, solveCubic)


------------------------------------------------------------------------------
type F4 k = E3 k

data SolveQuartic k = 
     SolveQuartic 
     {discrim4        :: k,                -- full
      discrim4_0      :: k,                -- is 0 if  f  has a triple root
      discrim4_1      :: k,                -- is 0 if  f  has two double roots
      resolvent       :: UPol k,           -- cubic resolvent
      solutionToCubic :: SolveCubic k,     -- for resolvent
      resolRoot       :: F4 k,             -- the chosen resolvent root 
      roots4          :: [F4 k],
      toExt4          :: k -> F4 k
     }
-- Here  solutionToCubic  also contains some useful attributes.


solveQuartic :: 
     (Field k, Field (ResidueI (Pol k)))
     =>
     GBasisOrNot -> GBasisOrNot ->                            -- mode1 mode2
     String -> k -> k -> k -> k -> Domains1 k -> SolveQuartic k
     -- suffix a    b    c    d    dK

-- Solving a quartic equation   f =  x^4 + a*x^3 + b*x^2 + c*x + d = 0 
-- by Ferraris's method.
-- solveCubic  is applied with  mode1.
-- mode2       is for final normalization of  rij  expressions. 

solveQuartic mode1 mode2 suffix a b c d dK = 
  case 
      char a
  of
  Just 2 -> error "\nsolveQuartic:  char k = 2.\n"
  Just 3 -> error "\nsolveQuartic:  char k = 3.\n"
  _      ->
            SolveQuartic {discrim4        = discr,
                          discrim4_0      = discr0,
                          discrim4_1      = discr1,
                          resolvent       = resol,
                          solutionToCubic = cubeSolution,
                          resolRoot       = y1',
                          roots4          = rootList,
                          toExt4          = kToF
                         }
  where
  [n1, n3, n4, n6, n12, n16, n18, n27, n64, n80, n128, n144, n192, n256] =
       map (fromi a) [1, 3, 4, 6, 12, 16, 18, 27, 64, 80, 128, 144, 192, 256]

  discr =
     n256*d^3 - n192*a*c*d^2 - n128*b^2*d^2 + n144*a^2*b*c^2*d - n27*c^4 
     + n144*a^2*b*d^2 - n6*a^2*c^2*d - n80*a*b^2*c*d + n18*a*b*c^3 + n16*b^4*d 
     - n4*b^3*c^2 - n27*a^4*d^2 + n18*a^3*b*c*d - n4*a^3*c^3 - n4*a^2*b^3*d 
     + a^2*b^2*c^2 

  discr0 = b^2 - n3*a*c + n12*d
  discr1 = n64*d - n16*b^2 + n16*a^2*b - n16*a*c - n3*a^4

  -- a1 = a*c - 4*d;  a0 = 4*b*d - a^2*d - c^2
  -- resol =  y^3 - b*y^2 + a1*y + a0

  a1    = a*c - n4*d
  a0    = n4*b*d - a^2*d - c^2
  unA   = cToUPol "y" dK n1      -- :: A k
  y     = varP n1 unA
  [bA, a1A, a0A] = map (ctr y) [b, a1, a0]

  resol = y^3 - bA*y^2 + a1A*y + a0A   -- the cubic resolvent

  cubeSolution = solveCubic mode1 suffix (- b) a1 a0 dK

  -- Kr, k_r = k(i, s, eta))  is the extension  k -- k(i, rt(-3), eta),
  -- it is built by  soveCubic.
  -- Below everything happens over  k_r.

  (i, _, _, _) =  i_ss_eta cubeSolution  -- each :: Kr k
                                    -- i^2 = -1,  s2^2 = 2,  s3^2 = 3, 
                                    -- eta  is a primitive root of  x^3 - 1.
  unKr      = unity i
  toKr      = kToKr            cubeSolution
  res_roots = SolveCubic.roots cubeSolution  -- :: [E3 k]

  anyE     = head res_roots  -- a sample element in  E
  (iI, dI) = resIDom anyE
  dPKr     = dom anyE             -- PKr = Pol (Kr k) 
  anyPKr   = resRepr anyE         -- a sample in  PKr

  -- We need to choose  y1  from  res-roots  which is in the ground field.
  -- This is the one of  minimal lpp  according to the above pp ordering.
  -- This is why `sort' is applied below.

  res_rootReprs = sortBy compByLpp $ map resRepr res_roots
                  where
                  cp = polPPComp anyPKr
                  compByLpp f g = case (polMons f, polMons g)
                                  of
                                  ([],         []         ) -> EQ
                                  ([],         _          ) -> LT  
                                  (_,          []         ) -> GT
                                  ((_, pp): _, (_, pp'): _) -> cp pp pp' 
  -- res_roots  are not needed further              

  y1Repr = head res_rootReprs

  ---------------------------------------------------
  -- Form the equations  r1^2 - (a^2 - 4*b + 4*y1),
  --                     r2^2 - (y1^2 - 4*d),
  --                     r3^3 - (p1^2 - 8*q1),
  --                     r3^3 - (p2^2 - 8*q2)    in  PKr
  --
  -- for   p_i, q_i <- Pk  defined below
  -- (recall that  r_i  are in the vaiables of (repr y1)).
  --
  -- Here  PKr = k_r[r3,r4,r1,r2,u,v,d]/I,  E3 k = PKr/I,  
  -- and we cannot put  E3 k
  -- to be a field. So we add to the ideal I the equations for r_i.

  [r3, r4, r1, r2, _, _, _] = varPs unKr anyPKr

  [m4, m8]     = map (fromi anyPKr)      [4, 8]
  [a', b', d'] = map (ctr anyPKr . toKr) [a, b, d]

  r1_eq =  r1^2 - (a'^2 - m4*b' + m4*y1Repr)
  r2_eq =  r2^2 - (y1Repr^2 - m4*d')      

  -- p = a  +- rt(a^2 - 4*b + 4*y1)   =  a +- r1
  -- q = y1 -+ rt(y1^2 - 4*d)         =  y1 -+ r2

  p1 = a' + r1
  p2 = a' - r1
  q1 = y1Repr - r2
  q2 = y1Repr + r2

  -- r3 = rt(p1^2 - 8*q1);  r4 = rt(p2^2 - 8*q2)

  {- x =  1/4 * (- p +- rt(p^2 - 8*q)).  That is

     x1 = 1/4 * (- p1 + rt(p1^2 - 8*q1))  = (- p1 + r3)/4
     x2 =                                 = (- p1 - r3)/4
     x3 = 1/4 * (- p2 + rt(p2^2 - 8*q2))  = (- p2 + r4)/4
     x4 =                                 = (- p2 - r4)/4
  -}
  r3_eq = r3^2 - p1^2 + m8*q1
  r4_eq = r4^2 - p2^2 + m8*q2

  Just gs = idealGens iI
  gs'     = let gens = r3_eq : r4_eq : r1_eq : r2_eq : gs
            in
            case mode2 of GBasisNot -> gens
                          _         -> gBasisWithRadicals gens
                                       -- ??
                                       -- (idealGens iI) are free of r_i ...

  iI' = iI {idealGens = Just gs'}
  dI' = Map.insert IdealKey (D1Ideal iI') dI

  y1' = Rsi y1Repr (iI', dI') dPKr 

  -- yi'  belong to the ring  F,  which is the extension of (E3 k) with the 
  -- radicals  r_i. 

  aF   = ctr y1' a'
  kToF = ctr aF . ctr anyPKr . toKr

  x1pre = (- p1) + r3   -- :: PKr
  x2pre = (- p1) - r3
  x3pre = (- p2) + r4
  x4pre = (- p2) - r4

  oneOn4   = ctr anyPKr $ toKr $ inv n4  -- 1/4 in PKr

  rootList = map (\x -> ctr aF (oneOn4 * x)) [x1pre, x2pre, x3pre, x4pre] 
                                                            -- :: [F k]







{- saved **************************************************************

type A  k = UPol k            -- for  A  = k[d]
type K1 k = ResidueE (A k)    --      K1 = k[d]/(d_equation)
type B  k = Pol (K1 k)        --      B  = K1[u,v,r]
type E  k = ResidueI (B k)    --      E  = B/I = k1(u,v,r)
type PE k = Pol (E k)         --      PE = E[rt_s1, rt_s2]
type F  k = ResidueI (PE k)   --      F  = PE/Ideal[rt_s1_eq, rt_s2_eq]

data SolveQuartic k = 
     SolveQuartic 
     {discrim4        :: k,                -- full
      discrim4_0      :: k,                -- is 0 if  f  has a triple root
      discrim4_1      :: k,                -- is 0 if  f  has two double roots
      resolvent       :: UPol k,           -- cubic resolvent
      solutionToCubic :: SolveCubic k,     -- for resolvent
      extensionDom4   :: Domains1 (F k),
      roots4          :: [F k],
      toExt4          :: k -> F k          -- field embedding 
     }

------------------------------------------------------------------------------
solveQuartic :: (Field k, FactorizationRing (UPol k), LinSolvRing (UPol k))
                =>
                k -> k -> k -> k -> Domains1 k -> SolveQuartic k
             -- a    b    c    d    dK

solveQuartic a b c d dK =  
                   SolveQuartic {discrim4        = discr,
                                 discrim4_0      = discr0,
                                 discrim4_1      = discr1,
                                 resolvent       = resol,
                                 solutionToCubic = cubeSolution,
                                 extensionDom4   = dF,
                                 roots4          = rootList,
                                 toExt4          = ctr unF . ctr unPE . kToE 
                                }
  where
  [n1, n3, n4, n6, n12, n16, n18, n27, n64, n80, n128, n144, n192, n256] =
       map (fromi a) [1, 3, 4, 6, 12, 16, 18, 27, 64, 80, 128, 144, 192, 256]

  discr =
     n256*d^3 - n192*a*c*d^2 - n128*b^2*d^2 + n144*a^2*b*c^2*d - n27*c^4 
     + n144*a^2*b*d^2 - n6*a^2*c^2*d - n80*a*b^2*c*d + n18*a*b*c^3 + n16*b^4*d 
     - n4*b^3*c^2 - n27*a^4*d^2 + n18*a^3*b*c*d - n4*a^3*c^3 - n4*a^2*b^3*d 
     + a^2*b^2*c^2 

  discr0 = b^2 - n3*a*c + n12*d
  discr1 = n64*d - n16*b^2 + n16*a^2*b - n16*a*c - n3*a^4

  -- a1 = a*c - 4*d;  a0 = 4*b*d - a^2*d - c^2
  -- resol =  y^3 - b*y^2 + a1*y + a0

  a1    = a*c - n4*d
  a0    = n4*b*d - a^2*d - c^2
  unA   = cToUPol "y" dK n1      -- :: A k
  y     = varP n1 unA
  [b', a1', a0'] = map (ctr y) [b, a1, a0]

  resol = y^3 - b'*y^2 + a1'*y + a0'

  cubeSolution = cubicExt b a1 a0 (Just Nothing) dK
  dE           = CubicExt.extensionDom cubeSolution
  res_roots    = CubicExt.roots        cubeSolution
  kToE         = CubicExt.toExt        cubeSolution

  y1 = head res_roots  -- how to choose a root?  **debug

  -- s1 = a^2 - 4*b + 4*y1;   s2 = y1^2 - 4*b;
  -- p = a +- rt(s1);  
  -- q = y1 -+ rt(s2)

  [a'', b''] = map kToE [a, b]  -- :: [E k]
  e4         = fromi a'' 4
  s1         = a''^2 - e4*b'' + e4*y1
  s2         = y1^2 - e4*b''

  -- Build  F = E(rt_s1, rt_s2) =  E[rt_s1, rt_s2]/Ideal[rt_s1_eq, rt_s2_eq]

  unE            = kToE n1
  varsF          = ["rt_s1", "rt_s2"] 
  unPE           = cToPol (lexPPO 2) varsF dE unE   -- :: PE k
  dPE            = upGCDLinSolvRing unPE Map.empty  -- domain PE
  [rt_s1, rt_s2] = varPs unE unPE                   -- :: [PE k]
  (s1', s2')     = (ctr unPE s1, ctr unPE s2) 
  rt_s1_eq       = rt_s1^2 - s1' 
  rt_s2_eq       = rt_s2^2 - s2' 
  rt_eqs         = [rt_s1_eq, rt_s2_eq]   -- Groebner basis for the ideal  

  (dI, iRad) = gensToIdeal rt_eqs [] [(IsGxBasis, Yes)]
                                     [(IsMaxIdeal, Yes)] dPE Map.empty

  unF = Rsi unPE (iRad, dI) dPE   -- :: F k  -- 1 in F
  dF  = upField unF Map.empty

  [rt_s1', rt_s2'] = map (ctr unF) [rt_s1, rt_s2]
  [y1', aF]        = map (ctr unF . ctr unPE) [y1, a'']  -- :: [F k]

  rootList = [aF + rt_s1',  aF - rt_s1',  y1' + rt_s2',  y1' - rt_s2']
                                                             -- :: [F k]
-}