------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------




-- Demonstration and test.
-- Constructing an algebraic cubic extension of  Q = Fraction Integer.
-- Computing in such extension.


module T_cubeext (t_cubeext_) 
where
import qualified Data.Map as Map (empty, lookup)

import Prelude hiding (minimum, maximum)
import DPrelude   
import Categs (CategoryName(..), Domain1(..), Subring(..), Ideal(..), 
                                              Property_Subring(..) )
import SetGroup (zeroS, isZero, power)
import RingModule 
import Fraction (Fraction(..))
import Pol 
import Residue    (Residue(..), resIdeal)
import SolveCubic (CubicExt(..), cubicExt)
import GBasis     (algRelsPols)


---------------------------------------------------------------------------
type Q = Fraction Integer  -- rational numbers - for coefficients

-- see also  cubicExt :
-- type A  k = UPol k            -- for  A  = k[d]
-- type K1 k = ResidueE (A k)    --      K1 = k[d]/(d_equation)
-- type B  k = Pol (K1 k)        --      B  = K1[u,v,r]
-- type E  k = ResidueI (B k)    --      E  = B/I = k1(u,v,r) 

t_cubeext_ =           -- Example. Build the extension of Q = Fraction Z
                       --                          with  f = t^3 - t + 1

  ([isFieldTest, fRootsTest, vtTest, relTest],    -- test, benchmark
   propsE, [roots, fRoots, vieteValues], rels     -- demo
  ) 
  where
  un         = 1:/1 :: Q
  (k0, a, b) = (zeroS un, -un, un) 
  dK         = upField un Map.empty

  cbExt = cubicExt k0 a b Nothing dK   :: CubicExt Q
  dE    = extensionDom cbExt
  roots = roots'       cbExt
  kToE  = toExt'       cbExt

  [x, y, z]         = roots 
  Just (D1Ring rE)  = Map.lookup Ring dE      -- look into ring E
  propsE            = subringProps rE         -- - for curiosity
  isFieldTest       = (lookup IsField propsE) == (Just Yes)

  -- Example of calculation in E.

  -- discr  = - (4:/1)*(power a 3) - (27:/1)*(power b 2)
  n1     = fromi x 1                                   -- 1 in E
  fRoots = [(power x 3) - x + n1 | x <- roots]  
                                           -- it must be [0,0,0], 0 of E
  fRootsTest  = all isZero fRoots
  vieteValues = [x+y+z, x*y+x*z+y*z, x*y*z]     
                                             -- testing Viete relations:
  vtCheck = map kToE [0:/1, a, -b]           -- this must give [0,a,-b]
  vtTest  = vieteValues == vtCheck   
    -- For these a,b, the Galois theory says E'= k1(x,y,z) = k1(x)
    -- and E':k1 = 3.  
    -- In particular,  y  has to express as a quadratic polynomial
    -- in  x  over  k1.  Let us test this.
    -- x,y  are the polynomial residues of  x',y' <- B = k1[u,v,r] 
    -- modulo the ideal I.  So we have to find the algebraic 
    -- relations between x',y' in B modulo I.
    
  [x', y'] = map resRepr [x, y]
  Just hs  = idealGens (resIdeal x)
  o        = lexPPO 2
  rels     = algRelsPols hs ["y", "x"] o [y', x']  
           -- the generators of algebraic relations for  y',x' viewed 
           -- modulo Ideal(hs) in  k1[u,v,r],  the relations to display
           --                                       in variables "y","x"
           -- rels  consists of the source cubic equation on  x  
           -- and a non-trivial expression of  y  via  x:
           --       y + ((3/23)*d)*x^2 + ((9/46)*d + 1/2)*x - (2/23)*d

  relCheck = map (smParse (head rels))
                 ["x^3 - x + 1",
                  "y + ((3/23)*d)*x^2 + ((9/46)*d + 1/2)*x - (2/23)*d"
                 ]
  relTest =  rels == relCheck




{- ----------------------- 
  putStr 
    ("f(root)-s, Viete relation, relation generator tests = "++)$ 
                        shows (fRootsTest,vtTest,relTest)$ ("\n\n"++)$
     ("(a,b) = "++) $ shows (a,b) $ ("\n\n"++)$
     ("discr = "++) $ shows discr $ ("\n\n"++)$
                        -- we see, discriminant is not a square in k
     ("properties of E = "++)$ shows propsE $      ("\n\n"++)$
     ("roots           = "++)$ shows roots $       ("\n\n"++)$
     ("f(roots)        = "++)$ shows fRoots $      ("\n\n"++)$
     ("vieteValues     = "++)$ shows vieteValues $ ("\n\n"++)$
     ("algebraic relations between y,x: \n"++) $ shows arelsCol "\n"
    )
-}




{- Timing ----------------------------------------------------------

Platform:  Linux Debian, PC i586, 166MHz, 32 Mbyte RAM. 

March 1999,  DoCon-2, -Onot,  ghc-4.02,  -M9m          0.87
                      -O                               0.56
   -- REPEAT it for  tuple41 t_cubeext_

April 1999.   Hugs-98-March-1999,  Z = Int (?),  17Mbyte heap  13.6

September 1999.  ghc-4.04,  DoCon-2, Z = Integer, -O            0.6  
-}
--------------------------------------------------------------------

