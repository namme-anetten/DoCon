------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2011
------------------------------------------------------------------------
------------------------------------------------------------------------




-- Demonstration, test, benchmark.



--------------------------------------------------------------------
{-  Demonstration 1.
    Matrix inversion, Residue, Polynomial arithmetic.

This program 
  builds the integer matrix  M,  3 x 6,  
  finds the generic solution of equation  M*x = 0   over the ring  Z
    of integers,
  adds rows to M to obtain the square matrix M',
  makes a rational matrix qM' by mapping :/1 to the elements of M,
  evaluates iM' = inverse qM',
  finds  iM'*qM'  to test that it is unity;
  builds the residue ring  R = Z/(5),  finds its property list  and 
    evaluates 2/3 in R; 
  reads (parses) from string the polynomials f,g  in variables ["x","y"] 
    with the coefficients from R,
  evaluates  gcd(f,g).
--------------------------------------------------------------------
-}





module T_demo1 (t_demo1_) 
where
import qualified Data.Map as Map (empty)

import DPrelude   (PropValue(..), Z, ctr, smParse, mapmap         )
import Categs     (Subring(..), Property_Subring(..), ResidueE(..))
import SetGroup   (zeroS                                          )
import RingModule (Ring(..), GCDRing(..), upField, eucIdeal       )
import Z          (dZ                                             )
import VecMatr    (Matrix(..), scalarMt                           )
import Fraction   (Fraction(..)                                   )
import Pol        (PolLike(..), Pol(), degRevLex, cToPol          )
import LinAlg     (solveLinear_euc, inverseMatr_euc               )


type Q = Fraction Integer   -- rational number field
type R = ResidueE Integer   -- for  Z/(b)
type P = Pol R              -- for  R[x,y]

t_demo1_ = (checks, (ker, iM'), (rProps, q, gcdFG))
                                         -- benchmark:  tuple31 t_demo1_
 where
                                       -- linear algebra over Integer, Q
 un  = 1     :: Z
 unQ = 1:/1  :: Q
 zrQ = zeroS unQ
 dQ  = upField unQ Map.empty      -- domain term of Q
 mM  = [[1,2,3,4,5,6],
        [5,0,6,7,1,0],
        [8,9,0,1,2,3]]            :: [[Integer]]

 v        = [0, 0, 0] :: [Integer]       -- right-hand part of system
 (_, ker) = solveLinear_euc mM v
 checkKer =                                              -- ker  must be
            [[-2627,   3320,  -60,  -80,   14055, -12298],
             [54511, -68890, 1245, 1657, -291624, 255171],
             [-5823,   7359, -133, -177,   31152, -27258]
            ]
 rows' = mM ++ [[0,2,0,4,0,2], [5,0,6,1,2,0], [0,2,0,1,2,1]]
 qM'   = mapmap (:/ un) rows'
 iM'   = Mt (inverseMatr_euc qM') dQ
                                    -- \m->Mt m <dom>  makes full matrix
 Mt mPrd _  = (Mt qM' dQ)*iM'       -- matrix product
 unM        = scalarMt qM' unQ zrQ  -- unity matrix of given size
 checkInvM' = mPrd == unM
 -----------------------------------------------------------------------
                                       -- arithmetics in R = Integer/(b)
 b  = 5 :: Integer
 iI = eucIdeal "bef" b [] [] []
                           -- Ideal (b) in R.  eucIdeal "bef"  completes
                           -- ideal attributes according to mode "bef". 
 r1 = Rse un iI dZ               -- unity residue by the prime base b
 dR = upField r1 Map.empty       -- the full domain description
                                 -- for the ring of r1 (R = Integer/(b))
 (_, rR)     = baseRing r1 dR    -- base ring to which r1 belongs
 rProps      = subringProps rR
 rFieldCheck = (lookup IsField rProps) == (Just Yes)
 [r2, r3, r4, r5] = map (ctr r1) [2, 3, 4, 5 ::Z]
                                      -- each n projects to domain of r1
 q          = r2/r3            -- more generic divide_m is also possible
 check2by3R = (q*r3 == r2)
 ------------------------------------------------------------------------
                                                   -- polynomials over R
 vars = ["x", "y"]
 ord  = (("drlex", 2), degRevLex, [])
                           -- The power product ordering description.
                           -- We could put instead of degRevLex any 
                           -- admissible function for the pp comparison.
 p1 = cToPol ord vars dR r1  :: P
                         -- Mapping from coefficient is the most correct
                         -- way to obtain some initial polynomial.
                         -- Here  r1  maps to the unity of  P = R[x,y].
 [x, y] = varPs r1 p1                           -- x,y as polynomials
 [f, g] = map (smParse p1) ["x*(x^5+1)", "y*(x+1)^2"]
                        -- Parses domain elements by the sample unP.
                        -- Alternative: [f,g] = [x*(x^5+p1), y*(x+p1)^2]
 gcdFG = gcD [f, g]
                 -- this must be (x+1)^2 because x^5+1 = (x+1)^5  over R
 gcdCheck = gcdFG == ((x + p1)^2)
 checks   = [ker == checkKer, checkInvM', rFieldCheck, check2by3R,
                                                            gcdCheck]



{-
  putStr 
    (-- shows e s
     -- prints any set element  e  prepending the string to  s;
     -- f $ x = f x  - this is to save a number of parentheses:

     shows test "\n"
      {-
     ("test for  ker, inv(M'), isField(R), 2/3 in R, gcD f g  =  "++
     ) $
     shows test $ ("\n\n"++) $

     ("kernel generators over Z = \n"++) $ shows (Mt ker dZ) $
                                                         ("\n\n"++)$
     ("inverse(qM')    = \n"++) $ shows iM'    $ ("\n\n"++)$
     ("properties of R = \n"++) $ shows rProps $ ("\n\n"++)$
     ("2/3 in R        = "  ++) $ shows q      $ ("\n\n"++)$
     ("gcd(f,g)        = "  ++) $ shows gcdFG  "\n"
      -}
    )
-}





{- Timing  ---------------------------------------------------------

This is for `checks' only:  tuple31 t_demo1_

Heap, Stack  are the minimal values at which the given minimal 
             running time is achieved:

Platform:  Linux Debian, PC i586, 166MHz, 32 Mbyte RAM. 

August 1999.  ghc-4.04, DoCon-2, Integer, Rse-Z, -O, 
                                                0.07 sec  -M33k -K4

-}









