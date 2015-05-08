------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2011
------------------------------------------------------------------------
------------------------------------------------------------------------




-- Demonstration, test, benchmark.  Finite field arithmetic.
-- Computing in the field  F  of 25 elements and in  F[y,z].

module T_finfield (t_finfield_)
where
import qualified Data.Map as Map (empty, lookup)

import DPrelude (ctr, smParse)
import Categs (CategoryName(..), Domain1(..), Subring(..), ResidueE(..))
import SetGroup (power)
import RingModule (Ring(..), GCDRing(..), eucIdeal, fromi, upField,
                                                         upEucFactrRing)
import Z   (dZ)
import Pol (PolLike(..), UPol(..), lexPPO, cToUPol, cToPol, varP)





------------------------------------------------------------------------
type R = ResidueE Integer    -- for Z/(d)
type F = ResidueE (UPol R)   -- represents  F = F25 = R[x]/(p)

t_finfield_ =
  ([divTest, x8Check, powCheck, gcdCheck],  gcd12, 
   [propsX, propsF],                        (p, [u,x'], powers, f1, f2)
  )                         
  -- Benchmark:  let (x, y, _, _) = t_finfield_  in (x, y)
  -- Demonstration example:
  -- let  uF = head $ tuple52 $ tuple44 t_finfield_
  --      s  = snd $ baseSet uF Map.empty 
  -- in   (osetCard s, osetList s)
  --                               --> (Fin 25, Just [0,1,x,..(4*x+1)])
  where
  d  = 5 :: Integer
  iI = eucIdeal "be" d [] [] [(d, 1)]  
  r0 = Rse 0 iI dZ 
  [r1, r2, r3, r4] = map (ctr r0) [1 .. (4 :: Integer)] 
                                                  -- project to residues
  d5       = upField  r0 Map.empty     -- full description for Z5
  (_, rZ5) = baseRing r0 d5            -- ring description
  propsZ5  = subringProps rZ5
  uX       = cToUPol "x" d5 r1  :: UPol R      -- 1 of Z5[x]            
  x        = varP r1 uX                        -- "x" as polynomial
  dX       = upEucFactrRing uX Map.empty       -- X = Z5[x]
  (_, rX)  = baseRing uX dX
  propsX   = subringProps rX

  p  = smParse uX "x^2+2"               -- irreducible over Z5, deg = 2
  iJ = eucIdeal "be" p [] [] [(p,1)]
  u  = Rse uX iJ dX  :: F               -- 1 of F = F25
  dF = upField u Map.empty              -- F25 = Z5X/(p) 
  rF = case Map.lookup Ring dF          -- another way to get 
       of                               -- ring description
       Just (D1Ring r) -> r
       _               -> error "\nRing not found in F25.\n"

  propsF = subringProps rF
            -- The Quotient Ring  F  is a field of 25 elements because
            -- p = x^2 + 2  is irreducible over Z5.  
            -- The elements of F correspond to polynomials  a*x+b,
            -- a, b = 0,1,2,3,4  <- Z5.
            -- Now let us do some computations:

  x' = ctr u x   -- project x to domain of u, that is to F
                 -- In particular:  x'^2  has to be  3  in F
                 --                 u/(x'+u) =  1/(x+1) =  3x+2  in F
  xpuInv = u/(x'+u)    
  ----------------------------------------------------------------------
  -- Now, find  f  from F  such that  [1,f,f^2..]  yields the full
  -- set F\{0} - this is possible, according to the theory.

  x8      = x'^8
  x8Check = x8 == u
                -- x^8  occurs 1 in F, so f = x  does not fit. Try 2x+3:
  [n1, n2, n3, n4] = map (fromi u) [1 .. 4]
  f      = n2*x' + n3
  powers = [power f i | i <- [0 .. 23]]
                          -- has to be [1, 2x+3, 2x+1, ... , 4x+4 ]
                          -- f fits iff (tail powers) does not contain 1
  powCheck = not (u `elem` (tail powers))
  divTest  = and [((a/b)*b) == a | a <- powers, b <- powers]
                                                   -- full division test
  ----------------------------------------------------------------------
                                                        -- gcd in F[v,w]
  o2       = lexPPO 2  -- lexicographic pp comparison for [y,z]
  b1       = cToPol o2 ["v", "w"] dF u    -- of B = F[v,w]
  [v, w]   = varPs u b1
  (f1, f2) = (v*(v^5+b1), w*(v+b1)^2)
  gcd12    = gcD [f1, f2]   
                    -- has to be (v+1)^2  - because v^5+1 = (v+1)^5 in B
  gcdCheck =  gcd12 == ((v + b1)^2)



{- ghc:
  putStr
    ( -- un-comment the needed part
      ("propsX       = "++)$ shows propsX $ ('\n':   )$
      ("propsF       = "++)$ shows propsF $ ("\n\n"++)$
      ("p            = "++)$ shows p      $ ('\n':   )$
      ("x   in F     = "++)$ shows x'     $ ('\n':   )$
      ("x^2 in F     = "++)$ shows x'p2   $ ('\n':   )$
      ("1/(x+1) in F = "++)$ shows xpuInv $ ("\n\n"++)$
      ("[f^i| f= 2x+3 in F, i<-[0..23]] = \n"++) $ shows powers $
                                                         ("\n\n"++)$
      ("[f1,f2] :: B =  "++)$ shows [f1,f2] $ ('\n':)$
      ("gcD [f1,f2]  =  "++)$ show  gcd12 
    )
-}





{- Timing ----------------------------------------------------------

let   (x,y,_,_) = t_finfield_  in  (x,y)

Platform:  Linux Debian, PC i586, 166MHz, 32 Mbyte RAM. 

April 1999.   hugs-98-March-1999, SmallResidue, 18Mbyte:   20.6 sec

August 1999.  ghc-4.04,  DoCon-2, -O,                       0.8
-}
