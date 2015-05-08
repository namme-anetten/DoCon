------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------




-- Demonstration, Test, Benchmark.
-- Symmetric function transformations.
-- See first the Manual.


module T_symfunc (t_symfunc_)
where
import qualified Data.Map as Map (empty)

import Data.Maybe (fromMaybe   )
import Data.List  (genericIndex)

import DPrelude   (alteredSum, product1, ct)
import SetGroup   (sub)
import RingModule (upField)
import Z          (dZ)
import Fraction (Fraction(..))
import VecMatr  (Matrix(..), scalProduct, scalarMt, isLowTriangMt,
                                                           mainMtDiag)
import Pol       (PolLike(..), Pol(..), lexPPO, cToPol)
import LinAlg    (inverseMatr_euc)
import Partition (PrttComp, pLexComp, prttsOfW, showsPrtt, kostkaTMinor,
                                                     permGroupCharTMinor
                 )
import AlgSymmF (SymPol(..), SymMon, SymmDecMessageMode(..), 
                                            cToSymPol, toSymPol)
import qualified AlgSymmF 
                 (to_e, to_e_pol,  to_m, to_m_pol,  to_h, to_h_pol,
                  to_p, to_p_pol,  to_s, to_s_pol
                 )
import T_grbas1 (pControlSum)




------------------------------------------------------------------------
type R = Fraction Integer


t_symfunc_ = (charKostka, discrTest, symMonToE)
 where
 un  = 1 :: Integer
 unR = un :/ un            -- of R = Fraction Integer
 dR  = upField unR Map.empty
 ------------------------------------------------------------------------
 -- Test  character matrix C for S(w),  Kostka number matrix.
 -- This all depends on the weight w.

 mtAltSum :: [[Integer]] -> Integer
 mtAltSum = alteredSum . map alteredSum

 cmCtrlSums, kmCtrlSums :: [Integer]
                                 -- control sums for  characterMatrix(w),
                                 -- kostkaMatrix(w)  for  w = [1..]
 cmCtrlSums = [1,2,3,3,9,9,-31, -2,-66,-434,-1136]
 kmCtrlSums = [1,1,1,1,3,0,-19,-27,-46,-291, -787, -396]

 charKostka w =     
             ([cmTest, kmTest, kmInvTest],            -- test, benchmark
              pts,  [mC, tK],  map mtAltSum [mC, tK]  -- extra things
             )
     where
     pts = prttsOfW [(w, 1)]               -- all partitions of weight w
     mC  = permGroupCharTMinor pts pts 
                   -- Its rows should be reciprocally orthogonal: 
                   -- permCharOrt mC -> "orthogonal".
                   -- Otherwise, it shows the first non-orthogonal pair.
     permCharOrt rows = no (zip pts rows)
         where
         no []                = "orthogonal"
         no [_]               = "orthogonal"
         no ((p, row): pairs) =  
           case  
                dropWhile ((== 0) . scalProduct row . snd) pairs
           of
           []           -> no pairs
           (q, row'): _ -> 
                         showsPrtt p $ ("  "++) $ showsPrtt q $
                         ("\n\n"++) $ shows row $ ("\n\n"++) $ show row'
                      
     cmTest = (permCharOrt mC) == "orthogonal"               &&           
              (mtAltSum mC) == (genericIndex cmCtrlSums (w-1))

     tK     = kostkaTMinor pts pts  :: [[Integer]]
     kmTest = isLowTriangMt tK                                && 
              all (== 1) (mainMtDiag tK)                      && 
              (mtAltSum tK) == (genericIndex kmCtrlSums (w-1))
     itK       = inverseMatr_euc tK
     unM       = scalarMt pts 1 0  :: [[Integer]]
     unM'      = Mt unM dZ
     tkByItK   = (Mt tK dZ)*(Mt itK dZ)      
     kmInvTest = tkByItK == unM'
 --------------------------------------------------------------------
 -- Polynomials, sym-polynomials, SymPol bases transformation
 --------------------------------------------------------------------
 pcp = pLexComp              :: PrttComp
 smp = cToSymPol pcp dR unR  :: SymPol R -- sample sym-polynomial

 toSymP :: Pol R -> SymPol R
 toSymP = fromMaybe (error "toSymPol _ f:  f is not symmetric") .
          toSymPol pcp

 listDiscr fs = (product1 (diffs fs))^2
                          where
                          diffs [_]     = []
                          diffs (f: fs) = (map (sub f) fs) ++ (diffs fs)
                          --
                          -- example: [a,b,c] -> (a-b)^2*(a-c)^2*(b-c)^2
 -----------------------------------------------------------------------
 -- Discriminant of  x1..xn  and elementary symmetrics  e1..en.
    
 discrSym 3 = ct smp [(  1:/1, [(4,1),(2,1)]       ), 
                      ( -2:/1, [(4,1),(1,2)]       ) :: SymMon R, 
                      ( -2:/1, [(3,2)]             ),  
                      (  2:/1, [(3,1),(2,1),(1,1)] ), 
                      ( -6:/1, [(2, 3)]            ) 
                     ]               
                      -- listDiscrim [_,_,_]  converted to SymPol R,
                      -- this is to test  toSymPol.
 discrSym 4 =                        
              ct smp [( 1:/1, [(6,1),(4,1),(2,1)] ) :: SymMon R, 
                      (-2:/1, [(6,1),(4,1),(1,2)] ),
                      (-2:/1, [(6,1),(3,2)]       ),
                      ( 2:/1, [(6,1),(3,1),(2,1),(1,1)] ),
                      (-6:/1, [(6,1),(2,3)] ),
                      (-2:/1, [(5,2),(2,1)] ), 
                      ( 4:/1, [(5,2),(1,2)] ), 
                      ( 2:/1, [(5,1),(4,1),(3,1)] ),
                      (-2:/1, [(5,1),(4,1),(2,1),(1,1)] ), 
                      (-4:/1, [(5,1),(3,2),(1,1)] ),
                      ( 4:/1, [(5,1),(3,1),(2,2)] ),
                      (-6:/1, [(4,3)] ),
                      ( 4:/1, [(4,2),(3,1),(1,1)] ), 
                      ( 4:/1, [(4,2),(2,2)] ), 
                      (-6:/1, [(4,1),(3,2),(2,1)] ), 
                      (24:/1, [(3,4)] )
                     ] 

                                -- control sum for e-expression of discr
 discrToE_check 3 = ((-4:/1, [3,0,1,0,0,0]), (-24:/1, [3,-1,1,2,0,0]))
 discrToE_check 4 = ((24:/1, [4,0,1,0,1,0,0,0,0,0,0,0]  ),
                     (-422:/1, [6,-5,-6,2,4,1,0,0,0,0,0,0]))
                       
 discrTest basisId n = ([toSymTest, discrToETest],  -- test, benchmark
                        discr, discrInE             -- demo
                       )
      where
      vars = map (('x' :) . show) [1 .. n]  -- ["x1","x2".."x<n>"]
      o      = lexPPO n
      unP    = cToPol o vars dR unR    -- 1 of P = R[x1..xn]
      xPols  = varPs unR unP           -- xi  as polynomials
      discr  = listDiscr xPols
      discrS = discrSym n              -- directly set sym-pol for
                                       -- discriminant [x1..xn]
      w             = deg discrS
      toSymTest     = (toSymP discr) == discrS  -- tests toSymPol
      (_, discrInE) = AlgSymmF.to_e_pol NoSymmDecMessages basisId 
                                        Map.empty (lexPPO w) discrS
                                                    -- testing  to_e_pol
      discrToETest =  pControlSum discrInE == discrToE_check n

      -- discrInE(3) = 
      --             -4*e1^3*e3 + e1^2*e2^2 - 8*e1^2*e4 +... - 8*e1^2*e4 
      -- discrInE(4) = 
      --             24*e1^4*e3*e5 - 27*e1^4*e4^2 - 8*e1^3*e2^2*e5 + ...
      --               - 27*e3^4 + 216*e3^2*e6 - 480*e3*e4*e5 + 256*e4^3

    --------------------------------------------------------------------
    -- Testing  to_e  of  
    -- m[j]   = symmetricOrbit( x^j         )  = power sum,
    -- m[jjj] = symmetricOrbit( x^j*y^j*z^j )
    --                                 - such m[j*k] are hard for  to_e. 

 symMonToE basisId j = 
          (test,                         -- test, benchmark
           m3, [h1, h3], pControlSum h3  -- demo: print, for example, h1
          )
          where
          w3 = 3*j
          m1 = ct smp ((unR, [(j, 1)]) :: SymMon R)  -- power sum
          m3 = ct smp ((unR, [(j, 3)]) :: SymMon R)
          noMessages = NoSymmDecMessages
          (_, h1)    = AlgSymmF.to_e_pol noMessages basisId Map.empty 
                                                          (lexPPO j ) m1
          (_, h3) = AlgSymmF.to_e_pol noMessages basisId Map.empty 
                                                          (lexPPO w3) m3
          test = (pControlSum h3) == (genericIndex m3CtrlSums (pred j))

 m3CtrlSums =
       [((a:/un, p), (b:/un, q)) | ((a, p), (b, q)) <-
        [
         ((1,[0,0,1]),             (0,[0,0,0])),            -- j = 1
         ((2,[1,0,0,0,1,0]),       (1,[0,1,2,1,0,-1])),         -- 2
         ((3,[2,0,0,0,0,0,1,0,0]), (-4,[0,3,0,0,3,2,-1,-1,-1])),
                                                                -- 3
         ((4,[3,0,0,0,0,0,0,0,1,0,0,0]),                        -- 4
                                  (-69,[2,0,4,2,-4,-2,3,0,0,0,-1,1])
         ),
         ((5,[4,0,0,0,0,0,0,0,0,0,1,0,0,0,0]),                  -- 5
                       (-106,[4,-1,-4,-1,-3,1,4,-1,1,2,-2,1,0,1,-1])
         ),
         ((6,[5,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0]),            -- 6
               (-127,[6,-7,-8,-3,5,-11,5,9,-4,-6,-2,4,0,-1,3,0,1,1])
         )
      ]]
    -- For example,
    -- h(4) =  4*e1^3*e9 - 4*e1^2*e2*e8 - 4*e1^2*e3*e7 + ...
    --          - 4*e4^3 - 12*e4*e8 + 4*e5*e7 + 2*e6^2 - 4*e12
    --------------------------------------------------------------------
    {- reserve *****************************************************
    -- Composing the transformation between the bases  <u>,<v>,
    -- <u>,<v> = "p","h" ... :
    -- (<u> --> <v> --> <u>)  has to be the identity.
    to be revised after other samples *****
    ph w = 
    sym_fs = [ct smp (unR, p) | p <- pts] -- all symmetric monomials
                                          -- (note  wt  above)
    sym_gs = snd $ foldl accum (Map.empty, []) sym_fs
                               where
                               accum (tab, hs) f = (tab', h:hs)
                                 where 
                                 (tab', h) = AlgSymmF.to_h "p" tab f
                                         
    sym_hs = snd $ foldl accum (Map.empty, []) sym_gs
                               where
                               accum (tab, hs) f = (tab', h:hs)
                                 where 
                                 (tab', h) = algSymmF.to_p "h" tab f
                                          
    -- test:  show (sym_fs == sym_hs)    
    -- Set also the letters "m","e","s".
    --------------------------------------------------------------------
    -- np = genLength pts
    -- ps = hPowerSums unP,  ps_n = genericTake n ps
    f = let  (e1:e2:e3:_) = es  
             (p1:p2:p3:_) = ps
             --e5            = es !! 4
        in   e2+e3
    sym_f = toSymP f              -- SymPol fullHomMons unR pcp dR
    -- fBack = fromSymPol cp vars sym_f
    fullHomMons = [(unR, p) | p <- pts]
     (_,h) = AlgSymmF.to_e_pol "mn" Map.empty o sym_f  
                                                    -- compare "m", "mn"
    -- See Manual and test the commutativity of the transformation 
    -- diagram. Say,   m --> p  ===  m --> s --> p,   and so on.
    -}






{- timing **********************************************************
                         


January 1998.

IBM PC-486, 120 MHz,    DoCon-1.06, 

ghc-2.08-linux,  -O compilation    time  ./run +RTS -H9000k





--------------------------------------------------------------------
--------------------------------------------------------------------
                       Kostka matrix tK


--------------------------------------------------------------------
 - w -> controlSum (transposed Kostka matrix tK), triangularity test

Z' = Integer

April 1999.
Hugs-98-March-1999,  17Mbyte heap    w = 10 |  23 sec
                                         11 |  52

ghc ?


--------------------------------------------------------------------
kostkaMInvTest
      - w -> transposed Kostka matrix tK, inverse(tK), check product.

  April 1999. 
  Hugs-98-March-1999,  17Mbyte heap    w = 11 |   59 sec
                                           12 |  147

  March 1999.
  i586, 166MHz, ghc-4.02, DoCon-2, -O, specs
      -------------------------------------
      12 |   7.6           minSpace =   10m
      -------------------------------------
      13 |  17.3                        20m 





--------------------------------------------------------------------
--------------------------------------------------------------------
Discriminant of [x1..xn].  Its conversion  to_e  - discrToETest.

April 1999.
Hugs-98-March-1999,  17Mbyte heap   
                                    mode = "mn"     "m"
                           n = 4 |  54 sec          144

DoCon:  show hDiscr4
March 1999.
i586, 166MHz, ghc-4.02, 
DoCon-2, -O, specs            3.4, minSpace 1m,    8.9,  10m

                              smParse.. takes 0.5 sec (?)


January 1998, 120MHz, -O, *Int*  n = 4 |  16.3 sec      19.8 


--------------------------------------------------------------------
to_e  of  m[jjj]:   (_,h) = to_e_pol mode Map.empty (lexPPO w) m[jjj]
                    pControlSum h

April 1999.
Hugs-98-March-1999,  17Mbyte heap   
                                      mode = "mn"    "m"
                           n = 4 |    4.4 sec        136
                               5 |   10.9
                               6 |   28.0
----------
DoCon
Run  show hMul43


March 1999 ...
DoCon-2, -O, specs
Z' = Integer ***      4       0.25,               7.4,  11m
                              minSpace=150k
                      5       0.8,     400k      space > 24m

                              smParse.. takes 0.6 sec (?)

--------------------------------------------------------------------
-- Direct test for transformation between the bases <u>,<v> ...

p - h - p.   test:  show (sym_fs==sym_hs)    

                                     wt |
  March 1999 ...
  DoCon-2, -O, specs,  Z'=Integer     9 |  15.3,  minSpace= 1200k
                                     10 |  46.2,            2500
********************************************************************
-}










