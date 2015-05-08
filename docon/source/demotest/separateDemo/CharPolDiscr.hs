-- Testing  charPol, matrixDiscriminant.

import qualified Data.Map as Map (empty)
import DExport

type K = Fraction Integer
type P = Pol K             -- K[x..]

main = 
 putStr $ concat
 ["chM =\n",            showsU chM "\n",
  "chP =\n",            showsU chP "\n",
  "|polMons discr| = ", shows (length $ polMons discr) "\n", 
  "discr =\n",          showsU discr "\n"
 ]
 where
 optU   = defaultShowOptions {parInShow = ParensNot}
 showsU :: DShow a => a -> String -> String
 showsU = showsUnparensUpper optU "()"
 {-
 mM = Mt [[1, 0, 0],
          [0, 2, 0],
          [0, 0, 1]] dZ   :: Matrix Integer
 -} 
 r1 = 1 :/ 1    -- [r0,_,r2,r3] = map (fromi r1) [0 .. 3]

 dK      = upField r1 Map.empty   :: Domains1 K
 xVars   = ["x11","x12","x13", "x22","x23", "x33"]
        -- ["x","y","z"]

 varNum = genericLength xVars
 ppO    = (("deglex", varNum), degLex, [])
 p1     = cToPol ppO xVars dK r1    :: P
 [p0, _, p2, _] = map (fromi p1) [0 .. 3]
 dP      = upLinSolvRing p1 Map.empty
 xPols   = varPs r1 p1  :: [P]   -- variables as polynomials

 [x11,x12,x13, x22,x23, x33] = xPols
                                             
 mRows = -- diagonalMt p0 [x+p1, y^2, z^3+p2, y^2]  
         [[x11, x12, x13],
          [x12, x22, x23],
          [x13, x23, x33]
         ]
 mM    = Mt mRows dP
 chM   = charMt  "la" mM
 chP   = charPol "la" mM
 discr = matrixDiscriminant mM
