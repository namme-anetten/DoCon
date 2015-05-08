-- DoCon-2.12   Demonstration, test, benchmark.

-- R-polynomials.  Testing arithmetics.


module T_rpol (t_rpol_)
where
import qualified Data.Map as Map (empty)

import DPrelude   (Natural, ctr, lexListComp, smParse)
import Categs     (ResidueE(..))
import RingModule (eucIdeal, upField)
import Z          (dZ)
import Pol        (Pol(..), RPol(..), lexPPO, rvarsVolum, cToRPol,
                   rvarsOfRanges, fromRPol, toRPol)

type F = ResidueE Integer   -- for  F = Z/(p)
type P = Pol  F
type R = RPol F

t_rpol_ = ([gp == gp'', grp == gp'], (vn, rvars), (gr, grp))
 where
 p  = 5 :: Integer
 iI = eucIdeal "bef" p [] [] []
 r0 = Rse 0 iI dZ
 dF = upField r0 Map.empty     
 [r1, r2, r3, r4] = map (ctr r0) [1 .. (4 :: Natural)]

 vcp    = flip (lexListComp compare) 
 ranges = [(1, 3), (0, 2)]
 vt     = (vcp, "x", ranges)  
          -- so,  r-variable set is  {x[i,j], i<-[1..3], i<-[0..2]},
          -- ordered lex-increasingly
 vn    = rvarsVolum    ranges
 rvars = rvarsOfRanges ranges
 o     = lexPPO vn
 unR   = cToRPol vt dF r1  :: R        -- 1 of  R = F[x[i,j]..]
 gr    = smParse unR "x_1_1 + 2*x_3_0"
 g     = fromRPol o gr     :: P
 m     = 2
 grp   = gr^m
 gp    = g^m
 gp'   = toRPol 'l' vt rvars gp
 gp''  = fromRPol o grp

{- (shows (vn, rvars)             ) $ ("\n\n"++) $
   (shows (gp == gp'', grp == gp')) $ ('\n':) $
   (shows (gr, grp)               ) $ ""
-}




{- more test for  RPol, Pol  ---------------------------------------
...
    ranges        = [(1, 4), (1, 4), (1, 4)]
    vt            = (vcp, "x", ranges)  
    vn    = rvarsVolum    ranges
    rvars = rvarsOfRanges ranges
    o     = lexPPO vn
    unR   = cToRPol vt dF r1  :: R        -- 1 of  R = F[x[i,j]..]
    rM    =
      map (map (smParse unR)) 
       [
        ["x_1_1_1 +2*x_1_1_2", "3*x_2_2_1*x_3_2_2^2", "2",   
                                                        "x_1_2_1+1" 
        ],
        ["x_1_1_1 +2",     "3*x_2_2_2^2",  "x_1_2_1+1",   "0"      ],
        ["x_3_3_1+x_2_1_2",  "3",          "x_1_2_1+1",  "x_4_1_1" ],
        ["0",                "x_2_2_3+1",  "2",          "x_1_2_1+1"]
       ]
    mM  = map (map (fromRPol o)) rM
    drm = det rM
    dm  = det mM
    dm' = toRPol 'l' vt rvars dm
  in
  putStr $ shows (drm==dm')  $ ('\n':) $
           shows drm         $ ('\n':) $
           shows dm
           "\n"
-}
