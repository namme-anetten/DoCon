------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge D.Mechveliani,  2011
------------------------------------------------------------------------
------------------------------------------------------------------------




-- Demonstration, test, benchmark.
-- Syzygies for polynomials from P = k[x1..xn], and vectors over P.
-- Groebner bases in a free module P^n.

module T_grbas2 (t_grbas2_)
where
import qualified Data.Map as Map (empty)

import DPrelude (Natural, PropValue(..), lookupProp, ct, ctr, product1, 
                 eqListsAsSets, smParse, mapmap
                )
import Categs (Domains1, Subring(..), Property_Subring(..), Ideal(..), 
               Property_Ideal(..), Property_IdealGen(..)
              )
import SetGroup   (zeroS, isZero, divides)
import RingModule (Ring(..), LinSolvRing(..), LinSolvLModule(..), 
                                              upField, upGCDLinSolvRing)
import Z        (dZ)
import VecMatr  (Vector(..))
import Fraction (Fraction(..))
import Pol (PolLike(..), UPol(..), Pol(..), VecPol(..),  degLex, varP, 
            degRevLex, cToUPol, cToPol, ecpTOP0, ecpTOP_weights, 
            upolMons, vpRepr, vpToV, vecPolToEPol
            )
import Residue  (ResidueI(..), gensToIdeal)
import GBasis   (isGBasis_e)
import T_grbas1 (pControlSum)




------------------------------------------------------------------------
type R  = Integer
type K  = Fraction R     -- Rational number field.
type P  = Pol K          -- K[x..]
type PZ = UPol Integer   -- Integer[x]
type CI = ResidueI PZ    -- to represent P/(g)  - cyclic integers


t_grbas2_ = (al, cocoa, abya, cyclInt)
 where
 (un, unK) = (1, 1:/1)      :: (R, K)
 dR        = dZ             :: Domains1 R
 dK        = upField unK Map.empty     
 -----------------------------------------------------------------------
 -- Groebner basis in the module  P^2  over  P = K[a,b,c,d]
 -- and syzygies for a list of elements of P^2.
 -- This example is taken from the book by O'Shea at al. 
 -- And they refer to  W.Adams & P.Loustaunau
 -- "An introduction to Groebner bases", AMS,Providence,RI,1994.

 al = (test, unp, eo, (fs, gs), rels)
      where
      (cp, vars) = (degRevLex, ["a", "b", "c", "d"])
      o          = (("degRevLex", 4), degRevLex, [])
      unp        = cToPol o vars dK unK   -- of P

                            -- build the P-module  mM = P^2  using 
                            -- the "TOP" e-comparison induced by cp:
      eo = (ecpTOP0 False cp, "a", [], cp)  
      fs = [VP (map (smParse unp) s) eo | 
                                 s <- [["a^2 + b^2"    , "c^2 - d^2"  ],
                                       ["a^3 - 2*b*c*d", "b^3 + a*c*d"],
                                       ["a   - b"      , "c   + d"    ]]
           ]                          
      gs'    = fst $ gxBasisM unp fs
      gs     = map vpRepr gs'
      gCheck = [g1, g2, g3, g4]
      g1 = map (smParse unp) ["a-b", "c+d"] 
      g2 = map (smParse unp) 
               ["b^2",  "-a*c/2 -b*c/2 +c^2/2 -a*d/2 -b*d/2 -d^2/2"]
      g3 = map (smParse unp) ["0",  
                              "a^2*c + b^2*c - a*c^2 + b*c^2 " ++
                              "+ a^2*d + b^2*d + a*d^2 - b*d^2"]
      g4 = map (smParse unp) 
               ["-2*b*c*d ",  
                " b^3 - a*b*c/2 + b^2*c/2 - a*c^2 + b*c^2/2 " ++
                     "- a*b*d/2 + b^2*d/2 + a*c*d + a*d^2 - b*d^2/2 "
               ]
      rels = syzygyGensM unp "" fs   -- syzygy generators
             -- it must consist of a single vector:
             -- [-a*b^3 + b^4 ..,  -a^2*c - b^2*c ..,  a^2*b^3 + b^5 ..]

      test  = [gs == gCheck, (mapmap pControlSum rels) == relCheck]
      relCheck = [[( (-1:/1,[1,3,0,0]), (3:/1,[-1,5,2,-2]) ),
                   ( (-1:/1,[2,0,1,0]), (-1:/1,[0,2,1,0])  ),
                   ( (1:/1,[2,3,0,0]) , (3:/1,[2,3,2,-2])  )
                 ]]
       -- demo:  show (Mt rels dP)
 ----------------------------------------------------------------
 -- Syzygies from CoCoA.   Compare them with DoCon ones.
 -- This example is taken from the CoCoA manual of 1990.

 cocoa = (test, unp, fs, eo, (rels, relsCo))
       where
       (cp, vars) = (degLex, ["x", "y", "z", "w"])
       o   = (("degLex", 4), cp, [])
       unp = cToPol o vars dK unK   -- of P = K[x,y,z,w]
       fs  = map (smParse unp) 
                  ["x*z^9    - y^3*w^6   ",  "y^8*w    - x^5*z^3 ",
                   "y^5*z^6  - x^4*w^5   ",  "y^13*z^3 - x^9*w^4 ",
                   "y^2*z^15 - x^3*w^11  ",  "y^21     - x^14*w^3",
                   "z^24     - x^2*y*w^17"
                  ]                 -- this occurs a Groebner basis

       rels'   = syzygyGens "g" fs           -- syzygies from DoCon
       relsCo' = mapmap (smParse unp)        -- from CoCoA
                   [
                    ["y^5",  "w^5",  "-x*z^3", "0", "0",  "0", "0"],
                    ["y^2*z^6", "0", "w^6",  "0",  "-x",  "0", "0"],
                    ["z^15",  "0", "0", "0", "y*w^6",   "0",  "-x"],
                    ["x^4",  "z^6", "-y^3*w", "0", "0",  "0",  "0"],
                    ["0",  "y^5*z^3", "x^5", "-w", "0",  "0",  "0"],
                    ["0",  "y^13",   "0",  "x^5", "0",  "-w",  "0"],
                    ["0", "x^4*w^4", "y^8", "-z^3", "0",  "0", "0"],
                    ["x^3*w^5", "0", "z^9", "0", "-y^3",  "0", "0"],
                    ["0",  "x^9*w^3", "0", "y^8", "0", "-z^3", "0"],
                    ["x^2*w^11", "0", "0", "0", "z^9", "0", "-y^2"]
                   ]
       -- We are going to verify the submodule equality for  rels'  and
       -- relsCo'.
       -- Build the P-module  mM = P^7  using the TOP e-comparison 
       -- induced by  cp  and  weights = map lpp fs
    
       wts    = map lpp fs
       eo     = (ecpTOP_weights False wts cp, "atl", wts, cp)
       rels   = [VP x eo | x <- rels'  ]
       relsCo = [VP x eo | x <- relsCo']
       zeroVP = zeroS (head rels)

       -- fs  occurs a Groebner basis.  And according to ordering
       -- chosen for P^7,  rels  is a Groebner basis too - as it is
       -- said by the theorem on the Taylor syzygies.  Hence, if we
       -- reduce  rels  mutually and compute  the Groebner basis 
       -- relsCoG for  relsCo,  we obtain  relsReduced  and relsCoG
       -- that must coincide as the sets:

       relsCoG     = fst $ gxBasisM unp relsCo
       relsReduced = reduceOnePath [] rels

       reduceOnePath gs []      = gs
       reduceOnePath gs (f: fs) = 
                        let r = fst $ moduloBasisM unp "cg" (gs ++ fs) f
                        in
                        if r == zeroVP then reduceOnePath gs      fs
                        else                reduceOnePath (r: gs) fs

       test = eqListsAsSets relsCoG relsReduced
 -----------------------------------------------------------------------
 -- Syzygies for the Abyankhar curve equation. 
 -- This example is from the paper by
 -- H.M.Moeller & F.Mora
 -- "New Constructive Methods in Classical Ideal Theory".
                                  
 abya = (test, unp, fs, eo, (rels, check))
      where
      (cp, vars) = (degLex, ["z", "y", "x"])
      o         = (("degLex", 3), cp, [])
      unp       = cToPol o vars dK unK
                               -- the Abyankhar curve  (t+t^5, t^3, t^4)
                               -- can be defined by the Groebner basis
      fs = map (smParse unp) ["z^2     - x*y     + z              ",
                              "y^4     - x*y*z   + x*y   - z      ",
                              "y^3*z   + y^3     - x^2*y + x*z    ",
                              "x*y^3   + y^2*z   - x^2*z + y^2    ",
                              "x*y^2*z + 2*x*y^2 - x^3   + y*z + y"
                             ]
      [f1, f2, f3, f4, f5] = fs
             -- Build the P-module  mM = P^5  using the TOP e-comparison 
             --           induced by  cp  and the weights  wi = lpp(fi):
      wts   = map lpp fs
      ecp   = ecpTOP_weights True wts cp
      eo    = (ecp, "at_", wts, cp)
      rels' = map Vec $ syzygyGens "g" fs      --test also "" mode
      rels  = [VP x eo | (Vec x) <- rels']
                                      -- this must be a Groebner basis -
                                      -- for the "g" mode and above wts
      (relsG, _) = gxBasisM unp rels 
      relsG'     = map vpToV relsG
      relsE      = map (vecPolToEPol eo) rels'
      relsGE     = map (vecPolToEPol eo) relsG'
  
              -- H.M.Moeller gives the reduced G-basis for the syzygies:
      check' = map Vec [[  f2, -f1,  p0,   p0,   p0],
                        [ m21, m22, m23,   p0,   p0],
                        [ m31, m32, m33,   p0,   p0],
                        [  p0, m42,  p1,  m44,   p0],
                        [ m51,  p0, m53,  m54,   p0],
                        [ m61,  p0,  p0,  m64,  m65],
                        [ p0 ,  p0,  m73,  p1,  m75]
                       ]
      check   = [VP x eo | (Vec x) <- check']
      (p0,p1) = (zeroS unp, unp)
      mr      = map (smParse unp)  :: [String] -> [P]

      [m21, m22, m23          ] = mr [ "y^3+x", "x"  , "-z" ]
      [m31, m32, m33          ] = mr [ "x*y+1", "z+1", "-y" ]
      [     m42,      m44     ] = mr [ "x", "-y" ]
      [m51,      m53, m54     ] = mr [ "y^2-x^2", "x", "-z" ]
      [m61,           m64, m65] = mr [ "x*y^2+y", "x", "-z" ]
      [          m73,      m75] = mr [ "x", "-y" ]

      modBasis vps   = fst .moduloBasisM unp "cg" vps
      check_by_relsG = map (modBasis relsG) check     
                                           -- these three must be zeroes
      relsG_by_check = map (modBasis check) relsG
      check_by_rels  = map (modBasis rels ) check

      [isGBrels, isGBrelsG] = map isGBasis_e [relsE, relsGE]
      test                  = 
                  [all isZero check_by_relsG, all isZero relsG_by_check,
                   all isZero check_by_rels, isGBrels, isGBrelsG]
                                   -- must be [True,True,True,True,True]

 -----------------------------------------------------------------------
 -- Arithmetic  of  Cyclic Integer ring
 -- modelled via Groebner basis over Integer.
 -- See  (Manual 'rsi.ex.c').
 -- The cyclic integers are the elements of  CI = Z[x]/(g),
 -- Z = Integer,  g = x^p' + x^(p'-1) +..+ 1,   p'= p-1, p prime.
 -- g = (x^p-1)/(x-1)   is irreducible.
 -- Concerning the arithmetics in CI,  see, for example, the book
 --                       [Ed]: H.M.Edwards "Fermat's last theorem ...".
 -- DoCon applies the constructor composition   ResidueI (UPol Integer)
 -- - using the underlying Groebner basis technique over an 
 -- Euclidean ring.
 -- The following program 
 --               builds the ideal in Z[x] and its residue ring CI,
 --               computes some *norms* and quotients in CI.

 cyclInt :: Natural -> ([Bool], [CI], [CI])
 cyclInt p = ([fieldZeroDivTest, divides f2 f1, divides nm2 nm1],
              [unCI, xCI],
              [f1, f2, fq]
             )
     where                                            
     substXPower :: PZ -> Integer -> PZ
     substXPower    f     n =  ct f [(a, e*n)| (a, e) <- upolMons f]
                 --
                 -- f(x) -> f(x^n).  
                 -- Here (ct f..) converts monomial list to domain of f.

     norm :: CI -> CI                      -- norm of cyclic integer r =
     norm  r@(Rsi f (iI, _) _) =                    -- product (orbit r)
                                product1 (r: (map (ctr r) fPowers))
                                where           
                                Just [g] = idealGens iI
                                p'       = ldeg g  -- p-1
                                fPowers  = map (substXPower f) [2 .. p'] 

                                          -- here  ctr r  projects to CI
     unP      = cToUPol "x" dZ 1         -- 1 of PZ
     dP       = upGCDLinSolvRing unP Map.empty 
     x        = varP 1 unP               -- x as element of P  
     g        = (x^p - unP)/(x-unP)
     (dI, iI) = gensToIdeal [g] [] bProps propsI dP Map.empty
                                               -- setting Ideal(g) in PZ
     eI       = (iI, dI)
     bProps   = [(IsGxBasis, Yes)]
     propsI   = [(Prime, Yes), (IsMaxIdeal, No)]
     unCI     = Rsi unP eI dP                    -- 1 of CI
     (_, rCI) = baseRing unCI Map.empty
     propsCI  = subringProps rCI
     xCI      = ctr unCI x            -- project x to residue ring CI
     fieldZeroDivTest =
                     [lookupProp p propsCI | p <- [IsField, HasZeroDiv]]
                     == [No, No]
     -- this example is taken from [Ed], section 4.2,exercise 11,
     --                                     and it is for  *** p = 5 ***
     f1 = smParse unCI "38*x^3 + 62*x^2 + 56*x + 29"
     f2 = smParse unCI " 3*x^3 +  4*x^2 +  7*x +  1"

                         -- f1  must be a multiple of  f2,
                         -- and norm(f1) must be a multiple of norm(f2):
     fq = f1/f2    
     [nm1, nm2, nmq] = map norm [f1, f2, fq]

