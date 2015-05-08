------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge D.Mechveliani,  2011
------------------------------------------------------------------------
------------------------------------------------------------------------




-- Demonstration, test, benchmark.
-- Groebner basis for polynomials over a Euclidean ring.

module T_grbas1 (pControlSum, t_grbas1_)
where
import qualified Data.Map as Map (empty)

import DPrelude   (ct, sum1, product1, smParse)
import Categs     (Dom(..), Domains1)
import SetGroup   (AddGroup(..), zeroS, isZero)
import RingModule (CommutativeRing(), LinSolvRing(..), upEucRing,
                                                upField, gxBasis_test)
import Z        (dZ)
import VecMatr  (Vector(..), vecRepr, constVec)
import Fraction (Fraction(..))
import Pol (PolLike(..), Pol(..), UPol(..), lexPPO, degLex, degRevLex, 
                         lexFromEnd, polMons, cToPol, upolMons, cToUPol)
import GBasis (isGBasis)


type R  = Integer
type K  = Fraction R  -- Rational number field.
type P  = Pol R       -- R[x..]
type PK = Pol K       -- K[x..]
type XK = UPol K      -- K[x]
type PX = Pol  XK     -- K[x][..]



pControlSum :: (CommutativeRing a, PolLike p, AddGroup (p a)) =>
                                 p a -> ((a, [Integer]), (a, [Integer]))
-- This is auxiliary for testing,
-- to avoid parsing or printing of large polynomials when testing or
-- benchmarking the programs.
-- It folds polynomial to the leading monomial and to the altered sum
-- of the rest monomials.  The power products are extracted from under 
--                                                               Vec.
pControlSum f =
  let
    mfromv (a, pp) = (a, vecRepr pp)
    z              = zeroS (sample f)
    zeroMon        = (z, constVec (Vec (pVars f)) 0 :: Vector Integer) 
  in
  case (isZero f, mfromv $ lm f)
  of
  (True, _) -> (mfromv zeroMon, mfromv zeroMon              )
  (_,    m) -> (m,              mfromv $ alsum '+' (pTail f))
               where
               alsum s f = let {m = lm f;  ft = pTail f}
                           in
                           if isZero f then  zeroMon
                           else            
                           if s == '+' then  m + (alsum '-' ft)
                           else              m - (alsum '+' ft)

------------------------------------------------------------------------
t_grbas1_ =   
  ([(coneTest, coneEqs), (bu1Test,          bu1Fs        ), 
    (bu2Test,   bu2Fs ), ([cstTest],        xQuads3      ),   
    ([arLTest], arLFs ), ([cyclRootTest 4], cyclRootEqs 4)
   ],
   ((moe1Test, moe1Fs), (moe2Test, moe2Fs), ([overPTest], overPFs')),
   cyclRootEqs
  )
  -- Test:        take  fst  of each of the above pairs.
  -- Benchmarks:  measure the time of
  --   cstTest, 
  --   arlTest,
  --   map pControlSum $ fst $ gxBasis $ cyclRootEqs n  for n = 5,6..
  where
  (un, unK)   = (1, 1:/1)  :: (R, K)
  dR          = dZ         :: Domains1 R
  dK          = upField unK Map.empty     
  yzV         = ["y", "z"]
  xyzV        = "x": yzV
  zyxV        = reverse xyzV
  coneVars    = ["u", "v", "x", "y", "z"]
  dlex3       = (("deglex", 3), degLex, [])  -- pp ordering
  dlex2       = (("deglex", 2), degLex, [])  --  
  lexFromEnd2 = (("", 2), lexFromEnd, [])    
  lexFromEnd3 = (("", 3), lexFromEnd, [])    
  --------------------------------------------------------------------
  -- Cone.  
  -- Deriving the cone equation in  K^3  from its polynomial 
  -- parameterization  fs = [x(u,v),y(u,v),z(u,v)].
  -- This is done by finding of the Groebner basis  gs  for  fs 
  -- respectively to (lexPPO 5) ordering for [u,v,x,y,z].
  -- (head gs) is the required equation.

  unCon = cToPol (lexPPO 5) coneVars dK unK  :: PK
                                         -- sample element for
                                         -- the domain Con = K[coneVars]
  coneEqs = map (smParse unCon) [" u^2   - v^2 - x ",
                                 " 2*u*v - y       ",
                                 " u^2   + v^2 - z "
                                ]
  coneTest =  (gs == coneGsCheck): (isGBasis gs): boos
                             where
                             (boos, (gs, _), _) = gxBasis_test 1 coneEqs

  -- the reduced Groebner basis must be
  coneGsCheck = map (smParse unCon)   
                [" x^2 + y^2      - z^2      ",   
                 " v^2 + (1:/2)*x - (1:/2)*z ",   " u*y - v*x   - v*z ",
                 " u*x - u*z      + v*y      ",   " u*v - (1:/2)*y    ",
                 " u^2 - (1:/2)*x - (1:/2)*z "]
  ----------------------------------------------------------------------
  -- Buch1.  Buchberger's  example No 1.

  unBu1 = cToPol dlex3 zyxV dK unK  :: PK     -- sample for the ring Bu1
  bu1Fs = map (smParse unBu1) [" y^2*x^2 - z^2   ", 
                               " z*y^2*x - z*y*x ",
                               " z*y*x^3 - z^2*x "
                              ]
  bu1Test =  (gs == bu1Check): (isGBasis gs): boos
                               where
                               (boos, (gs, _), _) = gxBasis_test 1 bu1Fs  

  bu1Check =                       -- the reduced Groebner basis must be
     map (smParse unBu1) [" y^2*x^2 - z^2     ",  " z*y*x^2 - z^3   ",
                          " z*y^2*x - z*y*x   ",  " z^2*y*x - z^2*x ",
                          " z^3*x   - z^2*x   ",  " z^3*y   - z^3   ",
                          " z^4     - z^2*x^2 ",  " z^2*x^3 - z^2*x "]
  ----------------------------------------------------------------------
  -- Buch2.  Buchberger's example No 2.

  unBu2 = cToPol (lexPPO 3) zyxV dK unK  
  bu2Fs = map (smParse unBu2) [" z*y^2  +  2*x   +  1:/2          ",
                               " z*x^2  -  y^2   -  (1:/2)*x      ",
                               " -z     +  y^2*x +  4*x^2  + 1:/4 "
                              ]
  bu2Test =  (gs == bu2Check): (isGBasis gs): boos  
                               where
                               (boos, (gs, _), _) = gxBasis_test 1 bu2Fs
                
  bu2Check =                       -- the reduced Groebner basis must be
      map (smParse unBu2)
          [("x^7 + (29/4)*x^6 - (17/16)*x^4 - (11/8)*x^3 + (1/32)*x^2"
            ++ "+ (15/16)*x + 1/4 "
           ),
           ("y^2 + (112/2745)*x^6 - (84/305)*x^5 - (1264/305)*x^4 " ++
            "- (13/549)*x^3 + (84/305)*x^2 + (1772/2745)*x + 2/2745 "
           ),
           ("z - (1568/2745)*x^6 - (1264/305)*x^5 + (6/305)*x^4 + " ++ 
            "(182/549)*x^3 - (2047/610)*x^2 - (103/2745)*x -2857/10980")
          ]
  ----------------------------------------------------------------------
  -- `Consistency'
  -- The consistency conditions for the three generic quadratic 
  --                                                   equations over K.
  cstVars = ["x","l","h","g","f","e","d","c","b","a"]
  unCst   = cToPol (lexPPO 10) cstVars dK unK  
  xQuads3 = map (smParse unCst) ["x^2*a + x*b + c",  "x^2*d + x*e + f",
                                 "x^2*g + x*h + l"
                                ]
  -- Set the pp-ordering with for exclusion of x (as above) and find  
  -- gs = reduced Groebner basis of  xQuads3.
  -- Then  gs  provides certain conditions on the values of  a..l
  -- for the consistency of the system in extension of K.
  -- For example, the elements of  gs  constant in x,  must equal zero, 
  -- otherwise, the system is inconsistent.
  -- 8 members of gs does not depend on x.

  cstTest  = (map pControlSum $ fst $ gxBasis xQuads3) == cstCheck
  cstCheck = 
      [((a:/un, p), (b:/un, q)) | ((a, p), (b, q)) <-
        [((1,[0,0,0,0,2,0,0,0,0,2]),(-5,[0,0,0,0,1,0,3,3,0,1])),
         ((1,[0,1,0,0,0,1,0,0,0,1]),(-5,[0,1,0,0,0,1,0,0,0,1])),
         ((1,[0,1,0,0,1,0,0,0,0,2]),(-3,[0,1,0,0,1,0,0,-2,4,0])),
         ((1,[0,1,0,0,1,0,1,0,0,1]),(1,[0,1,0,0,1,-2,3,0,2,-1])),
         ((1,[0,1,0,0,1,0,2,0,1,0]),(3,[0,1,0,1,0,5,1,3,-3,2])),
         ((1,[0,2,0,0,0,0,0,0,0,2]),(-5,[0,1,0,3,0,0,0,3,0,1])),
         ((1,[0,2,0,0,0,0,1,0,0,1]),(-3,[0,0,4,-2,0,0,1,0,0,1])),
         ((1,[0,2,0,0,0,0,2,0,0,0]),(-5,[0,1,0,3,3,0,1,0,0,0])),
         ((1,[1,0,0,0,0,1,0,0,0,1]),(1,[1,0,0,0,1,0,0,-1,1,1])),
         ((1,[1,0,0,0,1,0,0,0,0,1]),(1,[1,0,0,0,1,-1,1,0,1,0])),
         ((1,[1,0,0,0,1,0,1,0,1,0]),(-5,[1,0,0,0,0,2,0,1,-1,1])),
         ((1,[1,0,0,1,1,0,0,0,1,0]),(-5,[1,0,0,1,0,2,-1,1,-1,1])),
         ((1,[1,0,1,0,0,0,0,0,0,1]),(1,[1,1,0,0,0,0,0,-1,1,1])),
         ((1,[1,0,1,0,0,0,1,0,0,0]),(1,[1,1,0,0,-1,1,1,0,0,0])),
         ((1,[1,1,0,0,0,0,0,0,0,1]),(1,[1,1,-1,1,0,0,0,0,1,0])),
         ((1,[1,1,0,0,0,0,1,0,0,0]),(1,[1,1,-1,1,0,1,0,0,0,0])),
         ((1,[1,1,0,1,0,0,0,0,1,0]),(-5,[1,0,2,0,0,0,0,1,-1,1])),
         ((1,[1,1,0,1,0,1,0,0,0,0]),(-5,[1,0,2,0,1,-1,1,0,0,0])),
         ((1,[2,0,0,0,0,0,0,0,0,1]),(2,[1,0,0,0,0,0,0,1,1,0])),
         ((1,[2,0,0,0,0,0,1,0,0,0]),(2,[1,0,0,0,1,1,0,0,0,0])),
         ((1,[2,0,0,1,0,0,0,0,0,0]),(2,[1,1,1,0,0,0,0,0,0,0]))
       ]]
  ----------------------------------------------------------------------
  -- ArnLaz.  Arnborg-Lazard system. 
  -- They say, it is from a certain paper by
  -- Faugere, Gianni, Lazard, Mora  of 1989.

  unArL = cToPol dlex3 xyzV dK unK  
  arLFs = map (smParse unArL)
             [" x^2*y*z + x*y^2*z + x*y*z^2 + x*y*z + x*y + x*z + y*z ",
              " x^2*y^2*z + x^2*y*z + x*y^2*z^2 + x*y*z + x + y*z + z ",
              " x^2*y^2*z^2 + x^2*y^2*z + x*y^2*z + x*y*z + x*z + z + 1"
             ]
  arlGBas = fst $ gxBasis arLFs
  arLTest = (map pControlSum arlGBas) == arLCheck
                            -- Taking the three head monomials from each
                            -- entity of arlGBas must produce the list
  arLCheck = [((a:/un, p), m) | ((a, p), m) <- 
              [((1,[0,0,4]), ((4127:/42),[3,-3,3])),  
              ((1,[0,1,3]), ((-268:/21),[3,-3,3])), 
              ((1,[0,2,2]), ((73:/14),[3,-3,3])),   
              ((1,[0,3,1]), ((44:/21),[3,-3,3])),   
              ((1,[0,4,0]), ((-685:/42),[3,-3,3])),
              ((1,[1,0,3]), ((-500:/21),[3,-3,3])),
              ((1,[1,1,2]), ((158:/21),[3,-3,3])),
              ((1,[1,2,1]), ((-19:/6),[3,-3,3])),
              ((1,[1,3,0]), ((-5:/42),[3,-3,3])),
              ((1,[2,0,2]), ((99:/14),[3,-3,3])),
              ((1,[2,1,1]), ((-61:/14),[3,-3,3])),
              ((1,[2,2,0]), ((-1:/21),[3,-3,3])),  
              ((1,[3,0,1]), ((-36:/7),[3,-3,3])),
              ((1,[3,1,0]), ((92:/21),[3,-3,3])),
              ((1,[4,0,0]), ((803:/42),[3,-3,3]))
            ]]
  ----------------------------------------------------------------------
  -- Cyclic roots. 
  -- Do *** not confuse with the roots of x^n-1. ***
    
  {- They say, this example comes from the works of G.Bjoerck.   
      fs = [x1 + x2 + ... + xn,
            x1*x2 + x2*x3 + ... + x(n-1)*xn + xn*x1,
            ...
            x1*x2..*x(n-1) + x2*x3..*xn + ... + x(n-1)*xn..*x(n-3) 
                                                   + xn*x1..*x(n-2),
            x1*x2..*xn - 1
           ]
      They say, many systems compute the reduced Groebner basis  
      gs = [g1..gm]   for  n < 7  in a real time. But not further.
      For  n = 2,3,5,6  it appears that I = Ideal(gs)  has the zero 
      dimension. 
      That is for each i<- [1..n]  there exists  g <- gs such that 
      lpp(g) = xi^ni. 
      For  n = 4  dim > 0.
      Below  fs = [f1..fn]  is computed by the method:
      representing  f1  with  [x1..xn] = [mon_1..mon_n],  
                                       xi considered as polynomials, 
      initiate  vps = [x1..xn],
      for  k  from 1 to (n-1)  do
          vps' = [y1..yn] = rotate vps;
          fk = [mon1(k-1)*y1..mon_n(k-1)*yn] = [mon1(k)..mon_n(k)]
    -}

  cyclRootEqs n =  fn: (eqs [vpols] vpols 1)
      where
      vars  = map (('x' :) . show) [1 .. n]        -- ["x1".."xn"]
      o     = (("degRevLex", n), degRevLex, [])
      unp   = cToPol o vars dK unK
      vpols = varPs unK unp             -- [x1..xn] as polynomials
      fn    = (product1 vpols) - unp    -- x1*..+xn - 1 
      eqs (monpols:mpss) vps k =  
                         if  k == pred n  then  map sum1 (monpols: mpss)
                         else  
                         let rotate (x: xs) = xs ++ [x] 
                             vps'           = rotate vps
                             mps            = zipWith (*) monpols vps'
                         in  eqs (mps: monpols: mpss) vps' (succ k)   

  cyclRootGBas   = fst . gxBasis . cyclRootEqs
  cyclRootTest n = 
                 (map pControlSum $ cyclRootGBas n) == (cyclRootCheck n)
  cyclRootCheck 4 = [((a:/un, p), (b:/un, q)) | ((a,p), (b,q)) <-
                        [((1,[1,0,0,0]),(1,[0,1,1,-1])), 
                         ((1,[0,2,0,0]),(3,[0,1,0,3])),
                         ((1,[0,1,2,0]),(1,[0,1,2,0])),
                         ((1,[0,1,1,2]),(-1,[0,1,1,-2])),
                         ((1,[0,1,0,4]),(1,[0,1,0,4])),
                         ((1,[0,0,3,2]),(1,[0,0,3,2])),
                         ((1,[0,0,2,4]),(1,[0,2,0,-2]))
                    ]   ]
  ----------------------------------------------------------------------
  -- Groebner basis over a Euclidean ring.  Moe1.
  -- Moeller's example No 1  [Mo].    
  -- R = Integer

  yxV = ["y", "x"]  -- [Mo] writes of "graduated lexicographic ordering:
                    --           1 < x < y < x^2 < x*y < y^2 < x^3 < .."
                    --
  unMoe1   = cToPol dlex2 yxV dR un  :: P  -- = Pol R
  moe1Fs   = map (smParse unMoe1) ["2*y*x^2 - 17*y", "5*y^2*x - 3*x"]
  moe1Test = (gs == moe1Check): (isGBasis gs): boos
                              where
                              (boos, (gs, _), _) = gxBasis_test 1 moe1Fs  
                
                                   -- the weak reduced Groebner basis is
  moe1Check = map (smParse unMoe1)
                                  ["85*y^2  - 6*x^2",  "6*x^3   - 51*x",
                                   "2*y*x^2 - 17*y ",  "5*y^2*x - 3*x "]
  ----------------------------------------------------------------------
  -- Groebner basis over a Euclidean ring.  Moe2.
  -- Moeller's example No 2  
  -- from the manuscript of 1985  
  -- - as it is referenced by A.Kandri-Rody & D.Kapur.
  -- type R = Zc
                             -- "total degree ordering induced by y > x"
  unMoe2 = cToPol dlex2 yxV dR un  
  moe2Fs = map (smParse unMoe2)
                             ["7*x^2*y - 3*x", "4*x*y^2 - x*y", "3*y^3"]

  moe2Test =  (gs == moe2Check): (isGBasis gs): boos
                              where
                              (boos, (gs, _), _) = gxBasis_test 1 moe2Fs  

                                   -- the weak reduced Groebner basis is
  moe2Check =
           map (smParse unMoe2) ["3*x", "y*x^2", "y^2*x+2*y*x", "3*y^3"]

           -- In the paper, the third polynomial found is  y^2*x - y*x,
           -- but this due to the reduction specifics:
           -- 2yx mod 3x ... 2 mod 3 -> 2,  while in the paper it is -1.
  ----------------------------------------------------------------------
  -- Groebner basis over a Euclidean ring K[x],  K a field.  OverP.

  unX    = cToUPol "x" dK unK :: XK
  dX     = upEucRing unX Map.empty
  unXYZK = cToPol lexFromEnd3 xyzV dK unK  :: PK    
               -- any ordering needed in which  x^k < y,z  for any k > 0
               --
  unPX     = cToPol lexFromEnd2 yzV dX unX  :: PX  -- X[y,z]
  overPSts = ["x^2*y^2 - z^2", "x*y^2*z - x*y*z", "x^3*y*z - x*z^2"]
  overPFs      = map (smParse unXYZK) overPSts
  overPFs'     = map (smParse unPX  ) overPSts
  overPGs      = fst (gxBasis overPFs )
  overPGs'     = fst (gxBasis overPFs')
  overPGsCheck = map (smParse unXYZK)  
                              ["x^5*y^2 - x^3*y^2", "x^3*y^3 - x^3*y^2",
                               "x^3*y*z - x^3*y^2", "x*y^2*z - x*y*z  ", 
                               "z^2     - x^2*y^2"
                              ]
              -- Test:  though gs' is weak, still  gs == gs' (?)
              -- modulo the natural isomorphism K[x,y,z] <-> K[x][y,z]
  overPTest = overPGs == overPGsCheck && (map toXYZ overPGs') == overPGs
      where
                                                -- K[x][y,z] -> K[x,y,z]
      toXYZ f            = sum1 $ map convMon $ polMons f
      convMon (g, Vec p) = 
                      ct unXYZK [(a, Vec (n: p)) | (a, n) <- upolMons g]




{- reserve *********************************************************
    -- A parametric 31-degree curve.
    -- Taken from  
    -- A.Giovini et al. "One sugar cube, please ...",  ISSAC-91.
    vars = ["x","y","z","t"]
    ord  = (("",4),cp,[])
    cp (Vec (j:js)) (Vec (k:ks))  | j < k     = LT
                                  | j > k     = GT
                                  | otherwise = 
                                       degRevLex (Vec js) (Vec ks)
    sts = [ " x^31 - x^6 - x - y ",
            " x^8  - z           ",   
            " x^10 - t           "]
    DoCon and MuPAD overflow the memory.
    ------------------------------------
    Probably, the idea was to set the ordering in which 
    x^i > y^j*z^k*t^l   for i > 0, any j,k,l  and compute  gs
    which, probably, must contain at least two polynomials free of  x -?
    DoCon and MuPAD overflow 30 Mbyte memory.
    First, the coefficients grow enormously. 
    On the second,  gBasis  over  Z/(2311)  also needs too much of 
    memory. For it yields promptly the polynomials of more than 
    thousand monomials.
    Further, we tried to append  z^5 - t^4  to  fs  - knowing that
    this equation has to appear. But this had not helped.
    So, what was the idea of this example?
-}








