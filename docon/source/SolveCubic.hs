------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2014
------------------------------------------------------------------------
------------------------------------------------------------------------




{-# LANGUAGE ScopedTypeVariables, MonoLocalBinds #-}

module SolveCubic (E3, Kr, E3', SolveCubic(..), GBasisOrNot(..), solveCubic, 
                   CubicExt(..), cubicExt) 
where

-- Solving a cubic equation  f  by the Cardano formulae over any field  k,
--                                                      char(k) /= 2, 3.
-- The result is as follows. 
-- 1) The extensions            k -- k_r -- E = k_r[d, u, v]/I
--    to a commutative ring  E,
--    where
--      rt  := squareRoot,
--      k_r = k(r)  is the extesion with  r = rt(-3),  
--      d   = rt(discriminant(f)) ,
--      k_r -- E  is the extension with the roots of  f;
--      E  is a field when the discriminant(f) is not a square in  k_r.
--
-- 2) Expession for the roots of  f  as the representatives in  E.
--
-- d  is not put to coefficients because  (a) it is difficult to detect a
--    square root in algebraic extensions of the kind  Rational -- k1
--    (it is possible but is not simple).
--    (b) the quality of  Field k(r,d)  depends on the solution on (a).
-- 
-- solveCubic  reduces to  solveCubic_canonic.
--
-- solveCubic_canonic a b k   builds automatically the extension 
--                                                 k -- k_r -- E = k[d,u,v]/I
-- for the coefficients  a, b <- k  of 
--                                          f = t^3 + a*t + b
-- (this form of  f  is called `canonic'),
--
-- where  d  stands for the square root of discriminant  -4*a^3 -27*b^2.
--
-- RESTRICTION:   a /= 0    ?? **debug 
-- Below
-- u, v   are the Cardano cubic radicals. 
--
-- solveCubic_canonic  performs as follows. 
--
-- 1) Builds the field  k_r = k[r]/(r^2 + 3).
-- 2) Assigns  
--    discr = -4*a^3 - 27*b^2  -- the discriminant.
--    d_eq =  d^2 - discr      -- equation for  d = rt(discr). 
--
-- 3) Builds the ring  A = k_r[d,u,v]  and the ideal basis in A:
--                     d_eq  :  d^2 - discr
--                     r_eq  :  r^2 + 3  
--                     u_eq  :  u^3 - (3/2)*d*r + (27/2)*b 
--                     v_eq  :  v^3 + (3/2)*d*r + (27/2)*b 
--                     uv_eq :  u*v + 3*a,
-- 
-- -- the defining polynomials for the corresponding extension field 
-- elements.
-- 3) Finds   gs = GroebnerBasis [d_eq, u_eq, v_eq, uv_eq]  in  A.
-- 4) Builds the residue ring  
--                            E = A/Ideal(gs).
--
-- Defines the roots of  f  in  E  by the Cardano formulae: 
--                                        x1 = (1/3)*(u + v)  
--                                        x2 = (1/6)*(r*v - r*u - u - v)  
--                                        x3 = (1/6)*(r*u - r*v - u - v).
--
-- After this, one can compute various expressions of x_i in  E.


import qualified Data.Map as Map (empty)

import Prelude hiding (minimum, maximum)

import DPrelude   
import Categs (Domains1, Property_IdealGen(..), Property_Ideal(..),
                                                         ResidueE(..))
import SetGroup (MulSemigroup(..), isZero, times)
import SetGroup (unity)
import RingModule 
import VecMatr (Vector(..))
import Pol 
import GBasis  (gBasisWithRadicals)
import Residue (ResidueI(..), gensToIdeal)





-- ***************************************************************************
type Kr k = ResidueI (Pol k)        -- for  k_r = k(rt(-3)) = k[r]/(r^2 + 3)
type E3 k = ResidueI (Pol (Kr k))   -- for  E   = k1[d,u,v]/I(equations) 

data SolveCubic k =                                   -- see comments below
     SolveCubic 
     {
      dom_Kr   :: Domains1 (Kr k),
      i_ss_eta :: (Kr k, Kr k, Kr k, Kr k),  -- (i, s2= rt(2), s3=rt(3), eta),
                                            -- s2^2 = 2,  s3^2 = 3, 
                                            -- eta  a primitive root of x^3 -1
      f_Kr            :: UPol (Kr k),
      canonicPol      :: UPol (Kr k),
      discrim         :: Kr k,
      cardanoEqs      :: [Pol (Kr k)],
      cardanoGroebner :: [Pol (Kr k)],
      roots           :: [E3 k], 
      kToKr           :: k -> Kr k,      -- two embeddings
      k_rToExt        :: Kr k -> E3 k    -- 
     } 

data GBasisOrNot = GBasis | GBasisNot  deriving (Eq, Show)
--
-- GBasisNot  saves a lot of computation (on everage) by skipping gBasis, 
--            and somtimes may lead to a satisfactory expressions.



solveCubic ::            -- wait  OI  fix ? ** 
           (Field k, Field (ResidueI (Pol k)))
           =>        
           GBasisOrNot -> String -> k -> k -> k -> Domains1 k -> SolveCubic k
           -- mode        suffix    a    b    c    dK
            
-- Solve the equation  f(x) = 0,  f = x^3 + a*x^2 + b*x + c,
--
-- and build the atributes of the corresponding field extension
-- for a givien field  k  with  char k /= 2, 3. 
--
-- It is done by reduction to  solveCubic_canonic  -- see the comments there.
--
-- x = y - a/3   shifts  f  to  canonicPol = y^3 + p*y + q.
-- The result is 
--          SolveCubic {dom_Kr          = dKr,              -- domain of k_r
--                      i_ss_eta        = (i, s2, s3, eta),
--                      f_Kr            = f_overKr,
--                      canonicPol      = f_canonic,        -- y^3 + p*x + q 
--                      discrim         = discr,
--                      cardanoEqs      = carEqs,
--                      cardanoGroebner = gs,
--                      roots           = shiftedRoots, 
--                      kToKr           = toKr        -- two field embeddings 
--                      k_rToExt        = k_rToE      --
--                     } 
-- k_r = k(r) = k(i, s2, s3, eta)  is the field extension with  
--                          i, rt(2), rt(3), and a primitive root of x^3 - 1.
-- discrim  is the same for  f  and  canonicPol.
-- `roots'  are the roots to  f,  they differ from the roots of  canonicPol
-- in the a/3 shift;  they belong to  E k  built for  canonicPol.
-- cardanoGroebner  is the Groebner basis for  cardanoEqs.
--
-- The extension is described in the variables   "d", "u", "v",
-- (and reserved variables "r1", "r2", "r3", "r4")
-- which meaning is explained above.
--
-- `suffix'  is the suffix being add to these names, it is arranged in order
--           to differ on the output the extension levels obtained by
--           repeating  solveCubic, solveQuartic.


solveCubic mode suffix a b c dK =  
  case 
      char a 
  of
  Just 2 -> error "\nsolveCubic:  char k = 2.\n"
  Just 3 -> error "\nsolveCubic:  char k = 3.\n"
  _      -> 
            SolveCubic {dom_Kr          = dKr, 
                        i_ss_eta        = (i, s2, s3, eta),
                        f_Kr            = f_overKr,
                        canonicPol      = f_canonic,
                        discrim         = discr,
                        cardanoEqs      = carEqs,
                        cardanoGroebner = gs,
                        roots           = shiftedRoots, 
                        kToKr           = toKr,
                        k_rToExt        = k_rToE 
                       }

  -- f_canonic(y) =  y^3 + p*y + q,    p = b - a^2/3,
  --                                   q = (2*a^3 - 9*a*b + 27*c)/27
  where
  -- Prepare  p and q  for  canonicPol = y^3 + p*x + q.

  [n2, n3, n9, n27] = map (fromi a) [2, 3, 9, 27 :: Integer] 

  p = b - (a^2)/n3                      -- :: k
  q = (n2*a^3 - n9*a*b + n27*c) / n27   -- 
                                                  
  (toKr, dKr, (i, s2, s3, eta), discr, carEqs, gs, roots, k_rToE) = 
                                         solveCubic_canonic mode suffix p q dK
  kToE         = k_rToE . toKr  
  aOn3         = kToE (a/n3)
  shiftedRoots = map (\ x -> x - aOn3) roots 
  --
  -- f(x) = f_canonic(y-a/3),   y_i        are roots of f_canonic,
  --                            y_i - a/3  are roots of f.

  unKr      = unity i
  unP       = cToUPol "y" dKr unKr          -- 1  in Kr[y]
  y         = varP unKr unP                 -- y  in Kr[y]
  [p', q']  = map (ctr unP . toKr) [p, q]
  f_canonic = y^3 + p'*y + q'           -- :: UPol (Kr k)

  unPx         = cToUPol "x" dKr unKr   
  x            = varP unKr unPx
  [a', b', c'] = map (ctr unPx . toKr) [a, b, c]
  f_overKr     = x^3 + a'*x^2 + b'*x + c'        -- in Kr[x]





----------------------------------------------------- local auxiliary thing --
solveCubic_canonic :: 
     (Field k, Field (ResidueI (Pol k)))     
     =>        
     GBasisOrNot -> String -> k -> k -> Domains1 k -> 
     -- mode        suffix    a    b    dK            

            (k -> Kr k,        
             Domains1 (Kr k),  
             (Kr k, Kr k, Kr k, Kr k),  -- i, rt(2), rt(3), eta
             Kr k,                      -- discriminant
             [Pol (Kr k)],              -- Cardano equations
             [Pol (Kr k)],              -- groebnerBasis for Cardano equations
             [E3 k],                    -- roots
             Kr k -> E3 k               -- k_rToE 
            )                 

solveCubic_canonic mode suffix a b dK =  (kToKr,                 dKr, 
                                          (i', s2', s3', eta'),  discr, 
                                          cardanoEqs,            gs, 
                                          roots,                 k_rToE)
  where
  -- Build the field  
  --           Kr = k_r = k(i, s2, s3, eta) =  
  --                    k[i,s2,s3,eta]/(i^2 +1, s^2 -2, s^2 -3, eta^2 +eta +1)
  -- - here 
  --   i    is the imaginary unit,
  --   s2   a square root of  2,   s3  a square root of  3,  
  --   eta  a primitive cubic root of  1.

  unK       = fromi a 1
  etaSiVars = ["eta", "s2", "s3", "i"]
  unPk      = cToPol (lexPPO 4) etaSiVars dK unK   -- :: Pol k
  dPk       = upGCDLinSolvRing unPk Map.empty      -- domain of Pk

  [eta, s2, s3, i] = varPs unK unPk 
  [pk1, pk2, pk3]  = map (fromi unPk) [1, 2, 3]

  etaSi_eqs = [i^2 + pk1, s2^2 - pk2, s3^2 - pk3, eta^2 + eta + pk1]

  (dEtaSi, etaSiI) = gensToIdeal etaSi_eqs [] [(IsGxBasis, Yes)] 
                                           [(IsMaxIdeal, Yes)] dPk Map.empty

  unKr = Rsi unPk (etaSiI, dEtaSi) dPk         -- 1 in Kr

  [eta', s2', s3', i'] = map (ctr unKr) [eta, s2, s3, i]   -- in Kr 

  kToKr = ctr unKr . ctr unPk                  -- :: k -> Kr
  dKr   = upField unKr Map.empty  

  r = i'*s3'                                   -- :: Kr  a square root of -3

  -- Kr is ready.  The following happens over Kr.


  [n4, n27] = map (fromi unKr) [4, 27]  -- integer images in Kr
  [a', b']  = map kToKr [a, b] 

  discr = - n4*a'^3 - n27*b'^2

  vars = map (\s -> s ++ suffix) ["r3", "r4", "r1", "r2", "u", "v", "d"]
    --
    -- Variables for the cubic radicals over  k_r.
    -- r_i  are reserved, they can be used for expressing roots to quartic.

  -- To obtain more clear formulae for the roots x_i, define certain special
  -- ordering on the power products in [..u,v,d]:  compare them according to
  -- the weight list for the two matrix blocks:
  --                          -- u  v  d
  --                  [ r_i-part
  --                            [1, 1, 0],
  --                            [1, 0, 0],
  --                            [0, 0, 1] ],
  -- where the r_i part of 4 x 4 is by lexicographic.

  ppComp              -- \ (Vec js) (Vec ks) -> lexListComp compare js ks
         (Vec [r3,  r4,  r1,  r2,  u,  v,  d ])
         (Vec [r3', r4', r1', r2', u', v', d']) =
         case
             lexListComp compare [r3, r4, r1, r2] [r3', r4', r1', r2']
         of
         -- r_i  are of a higher precedence

         EQ -> (case compare (u + v) (u' + v')
                of
                EQ -> lexListComp compare [u, d] [u', d']
                v  -> v
               )
         v  -> v

  o   = (("deg2lex", 7), ppComp, [])
  unA = cToPol o vars dKr unKr
  dA  = upGCDLinSolvRing unA Map.empty  -- domain of A

  [u', v', d'] = drop 4 $ varPs unKr unA 

  [m0, m2, m3, m27] = map (times unA) [0, 2, 3, 27]  -- integer images in A
  (m3on2, m27on2)   = (m3/m2, m27/m2)                --

  [discr', a'', b'', r'] = map (ctr unA) [discr, a', b', r] -- embed to A

  cardanoEqs =  -- :: [Pol (Kr k)]  equations for  u, v, d
    if
      isZero discr
    then
      (if  isZero a  then  [d' - m0, u' - m0, v' - m0]   -- all roots are 0
       else
       [d',  u'^3 + m27on2*b'',  v'^3 + m27on2*b'',  u'*v' + m3*a'']
      )
    else  [d'^2 - discr',                  -- equations for  u, v, d
           u'^3 - m3on2*d'*r' + m27on2*b'',
           v'^3 + m3on2*d'*r' + m27on2*b'',
           u'*v' + m3*a'']

  gs = case mode of GBasisNot -> cardanoEqs
                    _         -> gBasisWithRadicals cardanoEqs

  (dI, iRad) = gensToIdeal gs [] [(IsGxBasis, Yes)] [] dA Map.empty
                                       --
                                       -- how to check/find maximality? **
  unE    = Rsi unA (iRad, dI) dA
  k_rToE = ctr unE . ctr unA

  [u, v, r3] = map (ctr unE) [u', v', r']   -- map to E

  -- The roots  x1, x2, x3  of  f  are represented by the Cardano formulas 
  -- in the radicals  u, v :

  [e3, e6] = map (fromi unE) [3, 6]
 
  roots = [(u + v)/e3,  (r3*v - r3*u - u - v)/e6,
                        (r3*u - r3*v - u - v)/e6]

  -- dE = upLinSolvRing unE Map.empty    







-- **************************************************************************
-- A cubic extension for a non-trival case,
-- with separating the field extension       k -- k(root(discriminant)).
--
-- cubicExt  reduces to  cubicExt_canonic.
-- cubicExt_canonic a b k   builds the radical extension tower
--                                               k -- k(d) -- E = k(d)(u,v,r)
--
-- for the given field  k,  and the coefficients  a, b   of 
--
--                          f = t^3 + a*t + b  over k
--
-- (this form of  f  is called `canonic'),
--
-- where  d  stands for the square root of discriminant  -4*a^3 -27*b^2.
--
-- RESTRICTIONS:  1) char(k) /= 2, 3,  2) f is irreducible,  3) a /= 0. 
-- Below
-- r                   square root of  -3, 
-- u,v                 Cardano cubic radicals. 
-- cubicExt  applies the operation  root 2 x  for  x <- k  returning
-- Just (Just y),  y <- k such that  y^2 = x  if there is such y in k. 
--
-- cubicExt  performs as follows. 
-- Assigns  discr = -4*a^3 - 27*b^2  of  f
--          dd =  minimal polynomial for  d  which is here 
--                    d^2 - discr   if  squareRoot(discr)  in  k  is Nothing
--                    d - squareRoot(discr)  (in k)   otherwise;
-- Builds the field  k1 = k(d) = k[d]/(dd) and the ring  B =  k1[u,v,r]
-- Puts  r,u,v,uv  to be the defining polynomials for the  
-- corresponding field elements 
--                     r :  r^2 + 3  
--                     u :  u^3 - (3/2)*d*r + (27/2)*b 
--                     v :  v^3 + (3/2)*d*r + (27/2)*b 
--                     uv:  u*v + 3*a;  
--
-- Finds   gs = GroebnerBasis [u,v,uv,r]  in  B;
-- Builds  E = B/I  for  the ideal  I = Ideal(gs)  in B,  this  E
-- representing an extension of  k1  containing the roots of  f;
-- Defines the _roots_ of  f  in  E  by the Cardano formulae: 
--                                   x = (1/3)*(u + v)  
--                                   y = (1/6)*(r*v - r*u - u - v)  
--                                   z = (1/6)*(r*u - r*v - u - v).
--
-- After this, we may compute various expressions of xi in  E  - see below.



type A   k = UPol k            -- for  A  = k[d]
type K1  k = ResidueE (A k)    --      K1 = k[d]/(d_equation)
type B   k = Pol (K1 k)        --      B  = K1[u,v,r]
type E3' k = ResidueI (B k)    --      E  = B/I = k1(u,v,r) 

data CubicExt k =                                 -- see comments below
     CubicExt {canonicPol'   :: UPol k,
               discrim'      :: k,
               mbDiscrimRoot :: MMaybe k,
               extensionDom  :: Domains1 (E3' k),   -- for canonicPol
               roots'        :: [E3' k], 
               toExt'        :: k -> E3' k          -- embedding
              } 

                                         -- wait  OI  fix ? **
cubicExt :: (Field k, FactorizationRing (UPol k), LinSolvRing (UPol k)) 
            =>        
            k -> k -> k -> MMaybe k -> Domains1 k -> CubicExt k
         -- a    b    c    mbDiscrRoot dK
            
-- Reduction to  cubicExt_canonic.
-- char k /= 2, 3.
-- The given polynomial is      f          = y^3 + a*y^2 + b*y + c.
-- x = y - a/3   shifts  f  to  canonicPol = y^3 + p*y + q.
-- The result is 
--            CubicExt {canonicPol'   = y^3 + p*y + q,
--                      discrim'      = ...
--                      mbDiscrimRoot = ...
--                      extensionDom  = ...  for canonicPol
--                      roots'        = ...  to  f
--                      toExt'        = kToE  
--                      }
-- discrim and (K1 k)  are the same for  f  and  canonicPol.
-- `roots'  are the roots to  f,  they differ from the roots of  canonicPol
-- in the a/3 shift;  they belong to  E k  built for  canonicPol.

cubicExt a b c mbDiscrRoot dK =  CubicExt {canonicPol'   = f_canonic,
                                           discrim'      = discr,
                                           mbDiscrimRoot = mbDiscrRoot',
                                           extensionDom  = dE,
                                           roots'        = shiftedRoots,
                                           toExt'        = kToE 
                                          }
  -- f_canonic(y) =  y^3 + p*y + q,    p = b - a^2/3,
  --                                   q = (2*a^3 - 9*a*b + 27*c)/27
  where
  [n1, n2, n3, n9, n27] = map (fromi a) [1, 2, 3, 9, 27] 

  p = b - (a^2)/n3
  q = (n2*a^3 - n9*a*b + n27*c)/n27

  (discr, mbDiscrRoot', dE, roots, kToE) = cubicExt_canonic p q mbDiscrRoot dK

  aOn3         = kToE (a/n3)
  shiftedRoots = map (\ x -> x - aOn3) roots 
  --
  -- f(x) = f_canonic(y-a/3),   y_i        are roots of f_canonic,
  --                            y_i - a/3  are roots of f.

  unP           = cToUPol "y" dK n1     -- 1  in k[y]
  y             = varP n1 unP           -- y  in k[y]
  [p', q']      = map (ctr unP) [p, q]
  f_canonic     = y^3 + p'*y + q'





-- local auxiliary thing -----------------------------------------------------
                                         -- wait  OI  fix ? **
cubicExt_canonic :: 
         (Field k, FactorizationRing (UPol k), LinSolvRing (UPol k)) 
         =>        
         k -> k -> MMaybe k -> Domains1 k ->
      -- a    b    mbDiscrRoot  dK

         (k,                  -- discr
          MMaybe k,           -- mbDiscrRoot'
          Domains1 (E3' k),   -- dE 
          [E3' k],            -- [x,y,z], 
          k -> E3' k          -- kToE
         )

-- Building the Extension  E  of the field  k  to include the roots
-- x,y,z  of  
--                          irreducible  f = t^3 + a*t + b,  a /= 0,
-- according to the Cardano formulae.
-- See above the formulation.
--
-- Here         discr = - 4*a^3 - 27*b^2.
-- mbDiscrRoot  
--             is for the case of a given result of  root 2 discr  in k:
--             Just (Just rad)  means  discr = rad^2,
--             Just Nothing     means  discr  is not square,
--             Nothing          unknown, apply root and see.
-- Examples:  Just Nothing  means "believe that  discr  is not a square",
--            Nothing       means "try to find a root or its absence".
--
-- It returns the tuple:
--    discr,
--    mbDiscrRoot'       -- the possibly found square root of discriminant,    
--    dE                 -- domain description for the field  E,
--    [x,y,z]            -- elements of E representing the above roots,
--    embedding function k -> E.
--
-- Example:  let {un = 1:/1 :: Q;  dK = upField un Map.empty}
--           in  cubicExt un (-un) Nothing dK 
--
-- builds the extension      (_, Just Nothing, dE, [x,y,z], kToE) 
-- expressing  Q -- Q(rootsOf(t^3-t+1)) = E.


cubicExt_canonic a b mbDiscrRoot dK =  (discr, mbDiscrRoot', dE, roots, kToE)
 where
 [unK, n4, n27] = map (fromi a) [1, 4, 27]  -- integer images in k
 unA   = cToUPol "d" dK unK                 -- 1 of A = k[d]
 dA    = upEucRing unA Map.empty            -- domain A
 dv    = varP unK unA                       -- "d" as element of A
 discr = - n4*a^3 - n27*b*b

 mbDiscrRoot' = case mbDiscrRoot of Just v -> Just v
                                    _      -> root 2 discr
                                         -- try to compute, if it is not given
 dd = case mbDiscrRoot'
      of
      Just (Just rad) -> dv - (ctr unA rad)        -- linear equation in "d"
      Just Nothing    -> dv*dv - (ctr unA discr)   -- regular case
      _               ->
                    error "\ncubicExtension a b _ _:  could not find whether \
                          \the discriminant is a square\nin  k.\n"

 ddI     = eucIdeal "be" dd [] [] [(dd, 1)]
 unK1    = Rse unA ddI dA   
 dK1     = upField unK1 Map.empty         -- domain of  K1 = k(d)
 d       = ctr unK1 dv              -- d <- K1 satisfies the equation dd
 varsUVR = ["u", "v", "r"]   -- variables for the cubic radicals over K1

            -- To obtain more clear formulas for the roots xi of f in E,
            -- we define certain special ordering on the power products 
            -- of  u,v,r:  compare according to the weight list
            --                                [[1,1,0],[1,0,0],[0,0,1]]:
 uvrComp (Vec [u, v, r]) (Vec [u', v', r']) =
                               case compare (u + v) (u' + v')  
                               of
                               EQ -> lexListComp compare [u, r] [u', r']
                               v  -> v
 o   = (("deg2lex", 3), uvrComp, [])
 unB = cToPol o varsUVR dK1 unK1
 dB  = upGCDLinSolvRing unB Map.empty  -- domain B
 d'  = ct unB d                        -- d image in B
 [u', v', r']  = varPs unK1 unB
 [m2, m3, m27] = map (times unB) [2, 3, 27]    -- integer images in B
 (m3_2, m27_2) = (m3/m2, m27/m2)               --
 kToB          = ctr unB . ctr unK1 . ctr unA
 [a', b']      = map kToB [a, b]            -- cast a,b to B
 radicals = [r'^2 + m3,           -- equations for u,v,r
             u'^3 - m3_2*d'*r' + m27_2*b',
             v'^3 + m3_2*d'*r' + m27_2*b',
             u'*v'+ m3*a']                 -- :: [B k]

 (gs, _)    = gxBasis radicals
 (dI, iRad) = gensToIdeal gs [] [(IsGxBasis, Yes)] 
                                [(IsMaxIdeal, Yes)] dB Map.empty
 unE  = Rsi unB (iRad, dI) dB
 kToE = ct unE . kToB
 dE   = upField unE Map.empty           -- E = B/iRad = K1(u,v,r)
 [u, v, r] = map (ctr unE) [u', v', r']       -- as elements of E

                 -- Finally, the roots  x1,x2,x3  of  f  are represented
                 -- by Cardano formulas in the radicals  u,v,uv,r :
 [e3, e6] = map (times unE) [3, 6]
 roots    = [(u + v)/e3,  (r*v - r*u - u - v)/e6,
                          (r*u - r*v - u - v)/e6]
