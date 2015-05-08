------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------




-- Demonstration, Test, Benchmark.
-- Polynomial factorization in k[x],  
-- k  a prime finite field  K = Integer/(q)
--    or its extension      K[t]/(g).


module T_pfactor (pFactorizControlSum, testFFPolFactrz, t_pfactor1_, 
                  testFactorBi, t_pfactor2_)
where
import System.Random (Random(..), mkStdGen)  -- non-standard, non-GHC

import qualified Data.Map as Map (empty)

import Data.List (nub)

import DPrelude (Length(..), -- class 
                 Natural, Z, InfUnn(..),  ctr, product1, sort, 
                                                    alteredSum, smParse)
import Categs   (Dom(..), OSet(..), ResidueE(..), Factorization)
import SetGroup (Set(..), unity, times, invertible, divides, eqFactrz, 
                                                 unfactor, gatherFactrz)
import RingModule (Ring(..), CommutativeRing(), GCDRing(..), Field(), 
                   FactorizationRing(..),  eucIdeal, upField, fromi,
                                    upEucFactrRing, numOfNPrimesOverFin)
import Z (dZ)
import Pol  
import T_grbas1 (pControlSum)





------------------------------------------------------------------------
pFactorizControlSum :: (CommutativeRing a, PolLike p, Ring (p a)) =>
                        Factorization (p a) -> ((a, [Integer]), Integer)
-- Also usable for timing:
-- a small output forces the factorization evaluation

pFactorizControlSum pairs = (foldl1 su (ps ++ ps'), alteredSum muls)
         where
         muls               = map snd pairs
         (ps, ps')          = unzip $ map (pControlSum . fst) pairs
         su (a, js) (b, ks) = (a+b, zipWith (+) js ks)
                         

------------------------------------------------------------------------
testFFPolFactrz :: Field k =>  Integer -> Factorization (UPol k) -> Bool
                               -- n       ftn
-- Test factorization of  ffPol(q,n) =  x^(q^n) - x 
-- over a finite field  K = GF(q)  (q a power of prime).
-- This polynomial we call an  ff-pol 
-- (universal Finite Field Polynomial).  
-- This is because for each factor  d  of  n,  the ffPol  
-- factorization enumerates all the irreducible normed polynomials of
-- degree  d  - see [La], chapter 7, exercises 1,2.
-- So, the main part of the test is to form the list  group(d)  of the 
-- factors in  ftn of degree  d  and verify that its length is 
-- numOfNPrimesOverFin(q,_).

testFFPolFactrz n ftn =  
  if
    n < 1 || null ftn  then
             error "\ntestFFPolFactrz n ftn:\nn > 0 and non-empty \
                   \factorization ftn needed.\n"
  else
  all (== 1) es                  &&  all ((== un) . lc) ps  && 
  nubDegs == nFactors            &&  testGroups degs        &&
  (x^(q^n) - x) == (product1 ps)

  where
  nFactors            = [k | k <- [1 .. n], divides k n]
  (ps@(p:_), es     ) = unzip ftn
  (dC,       un     ) = (dom p, unity (sample p))
  (x,        (_, sC)) = (varP un p, baseSet un dC)

  q = case osetCard sC of
                        Fin n -> n
                        _     -> error "\ntestFFPolFactrz _ ftn:  field\
                                       \ cardinality not detected.\n"
  degs    = sort $ map deg ps
  nubDegs = nub degs
      
  testGroups []      = True
  testGroups (d: ds) = 
                   (genLength ds') == (numOfNPrimesOverFin q $ factor d)
                   && (testGroups ds'')    
                   where
                   (ds', ds'') = span (== d) (d: ds) 


------------------------------------------------------------------------  
type K  = ResidueE Integer  -- for K  = Integer/(q)
type T  = UPol K            -- for T  = K[t]
type K1 = ResidueE T        --     K1 = T/(g) 
type X  = UPol K1           --     X  = K1[x]
type P  = Pol K             --     P  = K[x,y]
--                                 P1 = K1[x,y]


t_pfactor1_ q =  -- Factoring univariate polynomial over a finite field.
                                                  -- Prime  q  required.
  (overPrime, r1, t, overGeneric)
  where
                                   -- prepare  K = Integer/(q), T = K[t]
  iI = eucIdeal "bef" (q :: Integer) [] [] []
                    -- mode "bef" will, in particular, factor q to  ft,
                    -- further, it will be seen from iI that it is prime
  r0 = Rse 0 iI dZ
  [r1,r2,r3,r4,r5,r6,r7,r8,r9] = map (ctr r0) [1 .. (9 :: Integer)]
  dK  = upField r0 Map.empty
  unT = cToUPol "t" dK r1  :: T
  dT  = upEucFactrRing unT Map.empty
  t   = varP r1 unT        -- t <- T

  [n0,n1,n2,n3,n4,n5,n6,n7,n8,n9,n10,n11,n12] = 
                                               map (times unT) [0 .. 12]
                                                           -- int-s in T
  ----------------------------------------------------------------------
  overPrime =                                       -- factoring in K[t]
      ( [eqFactrz (factor f1)  f1_5check, 
         eqFactrz (factor knu) knu_13check
        ],
        [f1, knu]
      )
      where
      f1  = t^10 + t^7 + t^5 + t^3 + t^2 + n2*t + n2
      knu = t^8  + t^6 + n10*t^4 + n10*t^3 + n8*t^2 + n2*t + n8
      f1_5check = [(t^3 +n4*t +n3, 2), (t^4 + n2*t^2 +n3, 1)]
                                                            -- for q = 5
      knu_13check = [(t^3 + n8*t^2 + n4*t + n12,         1),
                     (t^4 + n2*t^3 + n3*t^2 + n4*t + n6, 1),
                     (t + n3,                            1) 
                    ]                                      -- for q = 13
  ----------------------------------------------------------------------
  overGeneric g =
      -- factoring in  K1[x],  K1 = T/(g), 
      -- g irreducible over K = Integer/(q),  T = K[t]
      -- Example:  q = 5,  g= t^3 - t - n2  yield the field GF(125). 

      ( [eqFactrz (factor f1') f1_5_g3_check, 
         eqFactrz (factor f2') f2_5_g3_check, 
         eqFactrz (factor f3') f3_5_g3_check
        ],
        unK1, 
        [x, t, f1']
      )
      where
      gI   = eucIdeal "" g [] [] [(g, 1)]
      unK1 = Rse unT gI dT         -- of K1
      dK1  = upField unK1 Map.empty
      unX  = cToUPol "x" dK1 unK1  -- of X = K1[x]
      x    = varP unK1 unX
      t    = ctr x $ ctr unK1 $ varP r1 $ unT  
                                    -- t in X  - local in `overGeneric'

      [i0,i1,i2,i3,i4,i5,i6,i7,i8,i9] = map (fromi x) [0 .. 9]

      f1' = x^10 + x^7 + x^5 + x^3 + x^2 + i2*x + i2
                   -- f1 from `overPrime' casted from K[x] to K1[x].
                   -- Over K1( q=5, g=t^3-t-2 ), it factors differently:
      f1_5_g3_check = 
                  [(x + i4*t,             2), (x + i2*t^2 +i2*t +i2, 2), 
                   (x + i3*t^2 +i4*t +i3, 2), (x^4 + i2*x^2 + i3,    1)
                 ]
                                                 -- K1 remains as in f1'
      f2'           = x^10 + i2*t*x^5 + t^2 + i2 
      f2_5_g3_check = [(x^2 + (t^2+t+i1)*x + t^2 + i4*t + i2, 5)]
                --
                -- here  (t^2+t+1)^5 = 2*t  and  (t^2+4*t+2)^5 = t^2+2  
                -- in K1 - which is found according to the (^q) operator 
                --                                       inversion in K1
      f3'           = unfactor f3_5_g3_check    -- for same K1 
      f3_5_g3_check = 
              [(x   + i2*t + i4,                                     2),
               (x^2 + (i3*t+i1)*x + i2*t^2 +t +i1,                   2),
               (x^4 + x^3 + (t^2+i1)*x^2 + i3,                       1),
               (x^5 +i3*x^4 +i4*x^3 +(t+i2)*x^2 +(i3*t+i1)*x + i4*t, 1),
               (x   + i2,                                            1)]

  -- TIMING  for K[t].
  -- For example,     
  --             let t            = DPrelude.tuple43 $ t_pfactor1_ 5
  --                 [n1, n2, n3] = map (fromi t) [1 .. 3]
  --                 f          = t^20 + n2*t + n1 
  --             in  pFactorizControlSum $ factor f
  --
  -- Example for  (K[t]/g)[x]:
  -- let
  --     (_, _, t, overGeneric) = t_pfactor1_ 5
  --     [n1, n2]              = map (fromi t) [1 .. 2]
  --     g                     = t^3 - t - n2
  --     x: tt: _              = DPrelude.tuple33 $ overGeneric g
  --     [m1, m2, m3]          = map (fromi x) [1 .. 3]
  -- in  
  -- factor (x^6 + m2*(tt^2 -m1)*x^3 + m3*tt)



------------------------------------------------------------------------
testFactorBi :: 
  FactorizationRing p => 
  p -> String -> String -> Natural -> Natural -> (Bool, Factorization p)

-- Set different primes  f, g  as the strings to parse by the given 
-- sample, then factor  f^n*g^m ...
-- Example:  testFactorBi unP "x^3 + y*(x+1)" "x^3 + y*(x^2*y + 2)" 1 1

testFactorBi smp fS gS n m =  (eqFactrz fts fts', fts')
             where 
             [f, g] = map (canAssoc . smParse smp) [fS, gS]
             fts    = [(p, e) | (p, e) <- [(f, n), (g, m)],
                                               e > 0, not $ invertible p
                      ]
             fts'= [(canAssoc h, i) | (h, i) <- factor $ unfactor fts]

      

t_pfactor2_ :: Natural -> 
                    (P, 
                     P -> P -> Z -> Int -> (Maybe (P, P), [(P, P)]),
                     Z -> Int -> [(Bool, P, P, Factorization P)]
                    )
t_pfactor2_ q =  (unP, family1, randRandFactor)   
 where
 iI            = eucIdeal "bef" q [] [] []
 r0            = Rse 0 iI dZ 
 [r1, r2, r3]  = map (ctr r0) [1, 2, (3 :: Integer)] 
 dK            = upField r0 Map.empty
 vars          = ["x", "y"]
 o             = lexPPO 2
 unP           = cToPol o vars dK r1 
 [x, y]        = varPs r1 unP               -- x,y in P
 kInP          = map (times unP) [0 .. (pred q)]  
 y0: y1: y2: _ = kInP
 kBut0         = tail kInP    -- k\{0}
 -----------------------------------------------------------------------
 family1 :: P -> P -> Z -> Int -> (Maybe (P, P), [(P, P)])
 family1    b    p    n    m   =  (firstWrong, irrPairs)
   where
   {- Example Family 1.  
      The main parameter is n.  Factor several "random"  f = g*h, 
      g,h  irreducibles,  deg_x f = deg_y f = 2*n,
      n = 3,4,..
      p = y+b,  b <- [0..(q-1)]    
      fs     = [g*h | g,h <- irreds]   -- deg_x f = deg_y f = 2*n
      irreds = [x^n + p*g | g <- gs]   
                             are irreducible by Eisenstein condition
      gs = [p^(n-1)*x^(n-1) + (a+b)*y*x^(n-2) + (a-b)*p^2*x + a | 
            a <- [1..(q-1)]
           ]
      m  = number of fi to take from fs and test
      Example:  family1 unP (y+b) 4 6
   -}
   gs = [p^(n-1)*x^(n-1) + (a+b)*y*x^(n-2) + (a-b)*p^2*x + a | 
                                                           a <- kBut0
        ]  
   irreds = [x^n + p*g | g <- gs]              -- some irreducibles of  
                                               --    deg_x = deg_y = n
   irrPairs = take m [(g, h) | g <- irreds, h <- irreds] 
   ffs      = [((g, h), factor (g*h)) | (g, h) <- irrPairs]
                            -- deg_x f = deg_y f = 2*n  for f = g*h ..
   isCorrect ((g, h), ftn) =  
                            eqFactrz ftn $ gatherFactrz [(g, 1), (h, 1)]

   firstWrong = case  map fst $ filter (not . isCorrect) ffs  of
                                                         x: _ -> Just x
                                                         _    -> Nothing 
     {- showsFFs []                  = id
        showsFFs (((g, h), ftn): ps) = 
                     shows g . (" *\n"++ ) . shows h . (" ->\n"++) .
                     shows ftn . ("\n\n"++ ) . showsFFs ps
     -}

 -----------------------------------------------------------------------
 -- Another family of examples:
 -- f from fs' are not square free in each A/(p) of linear p
    {-
    pr   = product1 [y-a | a <- kInP]  
                                   -- multiple of each linear p in A
    fs'  = [g^2 - pr^2*(b*x + b - unP)^2 | g <- irreds]
    ffs' = [(f, factor f) | f <- fs']
    ----------------------------------------------------------------
                                                  -- this is for fs'

    isAlmostCorrect (f, ftn) =  
                               f == (product1 [p^n | (p, n) <- ftn])

    wrong' = case dropWhile isAlmostCorrect ffs'  of  w:_ -> Just w
                                                      _   -> Nothing
    showsFFs' []             = id
    showsFFs' ((f, ftn): ps) = shows f  . (" ->\n"++) .
                               shows ftn . ("\n\n"++ ) .
                               showsFFs' ps
    -}

 -----------------------------------------------------------------------
 -- Family  randRandFactor.  
 -- Depends on  n,m <- Integer.  List of triplets (f, g, factor (f*g)),  
 -- f,g  pseudo-random non-constant normed polynomials from 
 --      k[x,y] chosen under the condition  deg_v f, deg_v g <= n
 --      for  v <- [x,y].   f,g  often occur irreducible.

 kRands = case mkStdGen 0 of 
                          gen -> map (ctr r0) (randoms gen :: [Integer])
                                             -- random elements of K
 randPols :: Z -> Int -> [P]            -- m random elements of P
 randPols    n    m = 
            take m $ map canAssoc $ filter (not . pIsConst) $ rps kRands
    where
    rps cs = f: (rps csRest)  where   
                              (f, csRest) = coefsToPol 'l' unP [n, n] cs
                                       
 randTrips n m = ts $ randPols n m
               where
               ts [f]     = []
               ts (f: fs) = [(f, g, factor (f*g)) | g <- fs] ++ (ts fs)

 randRandFactor :: Z -> Int -> [(Bool, P, P, Factorization P)]
 randRandFactor    n    m   = [((f*g) == unfactor ft, f, g, ft) | 
                               (f, g, ft) <- randTrips n m
                              ]

 -- Example of factoring  f^n*g^m  in  K[x,y],  prime f, g:
 -- let  
 --     unP      = DPrelude.tuple31 $ t_pfactor2_ 5
 --     (fS, gS) = ("x^2 + y", "x^3 + 2*y")
 -- in  testFactorBi unP fS gS 3 2  --->  (<test>, <factorization>)






{- Results and timing **********************************************

See DoCon  Manual,  Section on Performance comparison.

All the below information only adds some bits to the Manual. 


x^10 + x^7 + x^5 + x^3 + x^2 + 2*x + 2 =
             (x + 4*t)^2 * (x + 2*t^2+2*t+2)^2 * (x + 3*t^2+4*t+3)^2
           * (x^4 + 2*x^2 + 3)
Comparing this to factoring over K,  we see that the same polynomial 
first yields the factor   x^3 - x + 3,   as over K,  but than splits 
it further to the linear factors over  K1.
For example, we can easily test that  t  is its root in K1.
--------------------------------------------------------------------
K1[x], q = 5:

x^10 + 2*t*x^5 + t^2 + 2 =  (x^2 + (t^2+t+1)*x + t^2 + 4*t + 2)^5

Here  (t^2+t+1)^5 = 2*t  and  (t^2+4*t+2)^5 = t^2+2  in  K1
- which is found according to the (^q) operator inversion in K1.

--------------------------------------------------------------------
K1[x], q = 5:

f4 =   x^16 + x^15 + (m2*tt^2 +m1)*x^14 + (tt^2 +tt +m4)*x^13 
         + (tt^2 +tt +m2)*x^12 + tt*x^11 + (m3*tt^2 +m2*tt +m4)*x^10   
         + m3*tt^2*x^9 + (tt^2 +m2*tt +m4)*x^8 
         + (m2*tt^2 +m3*tt +m1)*x^7 + (-tt^2+m4)*x^6
         + (-tt^2+m2)*x^5 + (m3*tt+m2)*x^4 + (-tt^2+m2)*x^3 
         + (-tt^2+m1)*x^2 + m3*tt*x + tt 
f4Check = 
      [(x   + m2*tt + m4,                                           2),
       (x^2 + (m3*tt+m1)*x + m2*tt^2 +tt +m1,                       2),
       (x^4 + x^3 + (tt^2+m1)*x^2 + m3,                             1),
       (x^5 + m3*x^4 + m4*x^3 + (tt+m2)*x^2 + (m3*tt+m1)*x + m4*tt, 1),
       (x   + m2,                                                   1)
      ]

Timing for   eqFactrz f4Check $ factor f4   (= True)

June     2001.  ghc-5.00.1,  DoCon-2.02, -O    3.0 sec
December 1999.  ghc-4.04,    DoCon-2.01, -O    2.8 sec  heap = 230Kb(?)



********************************************************************
Factoring in  K[x,y].   

f = x^4 + y*(y^2*x^2 + 1)      -- irreducibles
h = x^4 + y*(y*x + y^2 + 2)    --
factor (f*h)

ghc-4.08,  DoCon-2.01, CG   1.7 ,     [y,x]:  1.7,  750Kb needed

ghc-4.08 profiling, [x,y]:  henselLift  takes  60  %   of time
                            and is called     3  times
                            GC  takes          27  % of what?
                            total alloc =      49  Mb
------------
Some information from the algorithm tracing:
toShift = True  p = y + 1   pS = y
f = (y^2)*x^6 + y^3*x^5 + (2*y^2+1)*x^4 + (y^6+y^4+y)*x^3 
     + (y^5+2)*x^2 + 3*y^4*x + y^8  
fS = (y^2+3*y+1)*x^6 + (y^3+2*y^2+3*y+4)*x^5 + (2*y^2+y+3)*x^4 
      + (y^6+4*y^5+y^4+y^3+y^2+y+1)*x^3 + (y^5+1)*x^2 
      + (3*y^4+3*y^3+3*y^2+3*y+3)*x 
      + y^8+2*y^7+3*y^6+4*y^5+4*y^3+3*y^2+2*y+1
fR_1    = x^6 + 4*x^5 + 3*x^4 + x^3 + x^2 + 3*x + 1
fRfactn = [x + 2, x^3 + x + 1, x^2 + 2*x + 3]



randRandFactor 7 **************************************************

f = f1 = x^7*y^7 + 2*x^7*y^5 + 3*x^7*y^2 + 4*x^6*y^7 + 2*x^6*y^4 
          + 4*x^6 + x^5*y^7 + 2*x^5*y^3 + 3*x^5*y^2 + 2*x^4*y^6 
          + 3*x^4*y^3 + x^4*y^2 + 2*x^3*y^7 + 4*x^3*y^3 + 2*x^2*y^7 
          + x^2*y^4 + x*y^7 + 2*x*y^4 + 4*x*y + y^6 + 2*y^2 + 4*y 
          + 2

g = f2 = x^7*y^7 + 3*x^7*y^6 + x^7*y^3 + 4*x^6*y^6 + 3*x^6*y^3 
          + 4*x^5*y^7 + 2*x^5*y^4 + 2*x^5 + 4*x^4*y^7 + x^4*y^4 
          + 3*x^4 + 2*x^3*y^5 + 2*x^3*y + 3*x^2*y^5 + x^2 + x*y^5 
          + 2*x + 4*y^3

lengths of factors and monomial sums (sorted) =
                                 [(18,(3,[66,72])),(23,(3,[79,90]))]

ghc-4.08 profiling:  henselLift  takes   30,  33  % of time 
                       and is called     11,   6     times,
                     GC  takes           65,  50  % of what?,
                     total alloc =     1282, 272  Mb                
--------------------------------------------------------------------
f = f1
g = f3 = x^7*y^6 + x^7*y^5 + 3*x^7*y^2 + 3*x^6*y^6 + 3*x^6*y^2 
          + 2*x^5*y^6 + 2*x^5*y^2 + x^5*y + 2*x^4*y + 3*x^3*y^6 
          + 2*x^3*y^4 + 4*x^3*y + 2*x^2*y^4 + 2*x^2*y + x*y^4 + 3*x
          + 4*y^6 + 2*y^3 + 3

lengths of factors and monomial sums (sorted) =
                                 [(19,(4,[60,67])),(23,(3,[79,90]))]

ghc-4.08 profiling:  henselLift  takes    30  % of time 
                       and is called       7  times,
                     GC  takes            65  % of what?,
                     total alloc =      1065  Mb                
--------------------------------------------------------------------
f = f1
g = f4 = x^7*y^7 + 2*x^7*y^6 + 4*x^7*y^3 + x^6*y^6 + 3*x^6*y^3 
          + 2*x^6*y^2 + 2*x^5*y^7 + 3*x^5*y^3 + 3*x^5 + x^4*y^2 
          + 4*x^3*y^6 + 2*x^3*y^3 + x^3*y + 3*x^2*y^6 + 3*x^2*y^2 
          + 2*x^2*y + 2*x*y^5 + 2*x*y + y^3 + 4*y^2

lengths of factors and monomial sums (sorted) =
                                 [(20,(1,[69,75])),(23,(3,[79,90]))]

ghc-4.08 profiling:  henselLift  takes    58,  35  % of time 
                       and is called       9,   5  times,
                     GC  takes            70,  47  % of what?,
                     total alloc =      3098, 260  Mb                
--------------------------------------------------------------------
f = f2
g = f3
lengths of factors and monomial sums (sorted) =
                                 [(18,(3,[66,72])),(19,(4,[60,67]))]

ghc-4.08 profiling:  henselLift  takes   45  % of time 
                       and is called      5  times,
                     GC  takes           42  % of what?,
                     total alloc =      157  Mb
-------------------------------------------------------------------
f = f2
g = f4
lengths of factors and monomial sums (sorted) =
                                [(18,(3,[66,72])),(20,(1,[69,75]))]

ghc-4.08 profiling:  henselLift  takes     32     % of time 
                       and is called      6,  9   times,
                     GC  takes             65     % of what?,
                     total alloc =         1210   Mb
-------------------------------------------------------------------
f = f3
g = f4
lengths of factors and monomial sums (sorted) =
                                [(19,(4,[60,67])),(20,(1,[69,75]))]

ghc-4.08 profiling:  henselLift  takes   30  % of time 
                       and is called      7  times,
                     GC  takes           63  % of what?,
                     total alloc =     1079  Mb                



randRandFactor 8 **************************************************

f = f1 = 
  x^8*y^8 + 3*x^8*y^4 + 3*x^8*y + 4*x^8 + 2*x^7*y^6 + 4*x^7*y^2 
   + x^7*y + 2*x^6*y^6 + 3*x^6*y^2 + 4*x^6 + x^5*y^6 + 2*x^5*y^3 
   + 4*x^4*y^8 + 2*x^4*y^4 + x^4*y + x^3*y^5 + 2*x^3*y^2 + 4*x^2*y^8
   + 2*x^2*y^7 + 2*x^2*y^3 + 3*x^2*y^2 + 2*x*y^8 + 4*x*y^5 + 2*x*y^2 
   + x*y + y^5 + 2*y + 2

g = f2 = 
  x^8*y^6 + x^8*y^5 + 2*x^8*y + 3*x^7*y^7 + 4*x^7*y^3 + x^7 
   + x^6*y^8 + x^6*y^6 + 2*x^6*y^2 + x^5*y^7 + x^5*y^3 + x^4*y^7 
   + x^4*y^5 + 2*x^4*y + 4*x^3*y^3 + 4*x^3 + 4*x^2*y^5 + 4*x^2 
   + 4*x*y^8 + 4*x*y^6 + 3*x*y^2 + y^3 + 4*y + 4

test: lengths of factors and monomial sums (sorted) =
                               [(24,(3,[89,98])),(28,(0,[101,111]))]

ghc-4.08 profiling:  henselLift  takes  22,  38  % of time 
                       and is called     7,   6  times,
                     GC  takes          63,  48  % of what?,
                     total alloc =     681, 275  Mb                
--------------------------------------------------------------------
f = f1
g = f3 = 
  x^8*y^7 + 2*x^8*y^4 + x^7*y^8 + 3*x^7*y^7 + x^7*y^4 + 3*x^6*y^8 
   + 3*x^6*y^6 + 2*x^6*y^3 + x^6 + 4*x^5*y^6 + x^5*y^3 + 2*x^5
   + 3*x^3*y^4 + 4*x^3*y + 4*x^2*y^6 + 4*x^2*y^2 + x*y^7 + x*y^3 
   + 3*x*y^2 + y^3 + 4*y + 4
 
lengths of factors and monomial sums (sorted) =
                               [(22,(3,[85,89])),(28,(0,[101,111]))]

ghc-4.08 profiling:  henselLift  takes   34   29  % of time 
                       and is called      7   11  times,
                     GC  takes           47   58  % of what?,
                     total alloc =      318, 944  Mb                

--------------------------------------------------------------------
f = f1
g = f4 = 
  x^8*y^8 + 3*x^8*y^5 + 4*x^7*y^8 + 2*x^7*y^3 + 2*x^6*y^8 
   + 4*x^6*y^4 + 3*x^6*y^3 + 4*x^5*y^8 + 2*x^5*y^4 + x^4*y^8 
   + 2*x^4*y^5 + 4*x^4 + 3*x^3*y^6 + 2*x^3*y^3 + 3*x^3 + 4*x^2*y^6
   + 2*x^2*y^5 + 2*x^2*y^2 + 2*x*y^8 + x*y^5 + 2*x*y + 4*y^7 + 2*y^6 
   + 3*y^2 + y + 1

lengths of factors and monomial sums (sorted) =
                              [(26,(4,[88,116])),(28,(0,[101,111]))]

ghc-4.08 profiling:  henselLift  takes    63,   31  % of time 
                       and is called       9,   13  times,
                     GC  takes            88,   89  % of what?,
                     total alloc =      6986, 2911  Mb                

--------------------------------------------------------------------
f = f1
g = f5 = 
  x^8*y^8 + 3*x^8*y^7 + 4*x^8*y^3 + 3*x^8*y^2 + x^7*y^3 + 2*x^7*y^2 
  + 3*x^7 + 2*x^6*y^8 + 2*x^6*y^2 + 4*x^5*y^4 + 4*x^4*y^8 
  + 3*x^4*y^7 + 3*x^4 + 2*x^3*y^7 + 3*x^3*y^6 + x^3*y^3 + x^3*y 
  + 2*x^3 + x^2*y^8 + x^2*y + 4*x^2 + 2*x*y^4 + x*y^3 + 4*y^8 
  + 3*y^5 + 3*y^4 + 3*y^3 + 4*y^2 + 3*y + 3
 
lengths of factors and monomial sums (sorted) =
                             [(28,(0,[101,111])),(30,(1,[105,110]))]

--------------------------------------------------------------------
f = f2
g = f3 
lengths of factors and monomial sums (sorted) =
                                 [(22,(3,[85,89])),(24,(3,[89,98]))]

ghc-4.08 profiling:  henselLift  takes   62,  23  % of time 
                       and is called     13,   8  times,
                     GC  takes           86,  69  % of what?,
                     total alloc =     7055, 700  Mb                
--------------------------------------------------------------------
f = f2
g = f4 
lengths of factors and monomial sums (sorted) =
                                [(24,(3,[89,98])),(26,(4,[88,116]))]

ghc-4.08 profiling:  henselLift  takes    30,   31  % of time 
                       and is called      12,    7  times,
                     GC  takes            91,   93  % of what? 
                     total alloc =      2881, 2735  Mb              
--------------------------------------------------------------------
f = f2
g = f5
lengths of factors and monomial sums (sorted) =
                               [(24,(3,[89,98])),(30,(1,[105,110]))]
--------------------------------------------------------------------
f = f3
g = f4 
lengths of factors and monomial sums (sorted) =
                                [(22,(3,[85,89])),(26,(4,[88,116]))]

ghc-4.08 profiling:  henselLift  takes   23   31  % of time 
                       and is called      7    7  times
                     GC  takes           85,  54  % of what?
                     total alloc =     1642, 240  Mb                


randRandFactor 9 ***************************************************

f = f1 = 
  x^9*y^9 + 2*x^9*y^7 + 3*x^9*y^6 + 3*x^9*y^2 + 4*x^9*y + x^9 
   + x^8*y^9 + 4*x^8*y^5 + 4*x^8*y^4 + 2*x^7*y^4 + 4*x^7*y^3 
   + x^7*y^2 + 4*x^6*y^8 + 2*x^6*y^7 + 3*x^6*y + 3*x^6 + 3*x^5*y^2 
   + x^5*y + 4*x^5 + 4*x^4*y^5 + 2*x^4*y^4 + 4*x^3*y^7 + 2*x^3*y^6 
   + 3*x^3*y^5 + x^2*y^9 + 2*x^2*y^6 + 2*x^2 + 2*x*y^9 + x*y^6 
   + x*y^5 + 2*x + 2*y^9 + 3*y^8 + 4*y^7 + y^3 + y^2 + y + 1

g = f2 =
  x^9*y^8 + x^9*y^7 + 2*x^9*y^5 + x^9 + 3*x^8*y^8 + x^8*y^3 + x^8*y 
   + x^8 + x^7*y^9 + 4*x^6*y^8 + 3*x^6*y^7 + 4*x^6*y + 3*x^6 
   + 4*x^5*y^8 + x^5*y + x^5 + x^4*y + x^4 + 4*x^3*y^9 + 2*x^3*y^3 
   + x^3*y + x^3 + x^2*y^5 + x^2*y^4 + 4*x*y^6 + 3*x*y^5 + 2*x*y^4 
   + 2*x*y^3 + 4*y^8 + y^7 + 2*y^6 + 2*y^2 + 3*y

lengths of factors and monomial sums (sorted) =
                             [(33,(2,[131,142])),(38,(4,[163,165]))]

ghc-4.08 profiling:  henselLift  takes   32,   11  % of time 
                       and is called      7,    8  times
                     GC takes            52,   79  % of what?
                     total alloc =      477, 3382  Mb                
---------------------------------------------------------------------
f = f1 
g = f3 =
  x^9*y^8 + 2*x^9*y^7 + x^9*y^6 + 2*x^9*y + x^8*y^9 + 3*x^8*y^4 
   + 3*x^8*y^2 + 4*x^7*y^4 + 4*x^7*y^3 + 3*x^6*y^6 + x^6*y^5 
   + 2*x^6*y^3 + 2*x^5*y^7 + 4*x^5*y^6 + x^4*y^7 + 4*x^4*y^6 + 2*x^4 
   + 3*x^3*y^8 + 3*x^3*y^7 + x^2*y^9 + 3*x^2*y^7 + 3*x*y^7 + 2*x*y^4 
   + x*y^3 + x*y^2 + 4*y^8 + 3*y^7 + 3*y^6 + 3*y^2 + 2*y + 1

lengths of factors and monomial sums (sorted) =
                             [(31,(3,[128,155])),(38,(4,[163,165]))]

ghc-4.08 profiling:  henselLift  takes   18,   17  % of time 
                       and is called     13,    5  times
                     GC  takes           88,   72  % of what?
                     total alloc =     6851, 1512  Mb                
---------------------------------------------------------------------
f = f1
g = f4 =
  x^9*y^9 + 2*x^9*y^8 + 2*x^9*y^7 + x^9*y^3 + 4*x^9*y^2 + 3*x^9 
   + 2*x^8*y^9 + 4*x^8*y^7 + x^8*y^2 + 4*x^8*y + 3*x^7*y^6 
   + 4*x^7*y^5 + 2*x^7*y^4 + x^7 + 2*x^6*y^9 + 2*x^6*y^8 + 3*x^6 
   + 2*x^5*y^8 + 3*x^5*y^7 + 2*x^5 + 3*x^4*y^9 + 4*x^4*y^2 
   + 3*x^4*y + 2*x^4 + 2*x^3*y^4 + 4*x^3*y^3 + 4*x^2*y^5 + 3*x^2*y^4 
   + 4*x^2*y^3 + 3*x^2*y^2 + 4*x*y^6 + 4*x*y^5 + 4*y^9 + 3*y^8 
   + 4*y^7 + 2*y^4 + y^3 + 2

lengths of factors and monomial sums (sorted) =
                             [(38,(4,[163,165])),(38,(4,[170,179]))]

ghc-4.08 profiling:  henselLift  takes    20,   16  % of time 
                       and is called      14,    6  times
                     GC  takes            70,   72  % of what?
                     total alloc =      2963, 2358  Mb                
---------------------------------------------------------------------
f = f1
g = f5 =
  x^9*y^9 + x^9*y^8 + 4*x^9*y^4 + 3*x^9*y + x^9 + 2*x^8*y^9 
   + x^8*y^8 + x^8 + x^7*y^9 + 2*x^7*y + 4*x^7 + 2*x^6*y^5 
   + 2*x^5*y^7 + x^5*y^6 + 3*x^5*y + 2*x^5 + x^4*y^9 + 4*x^4*y^7
   + 4*x^4*y^6 + 4*x^4*y^3 + 4*x^4*y^2 + x^3*y^3 + 2*x^3*y^2
   + 4*x^3*y + 3*x^3 + x^2*y^4 + x^2*y + 3*x^2 + x*y^3 + 2*x*y^2 
   + 3*x + 3*y^9 + 4*y^4 + 2*y^3 + 3*y^2 + 1
--------------------------------------------------------------------
f = f2
g = f3
lengths of factors and monomial sums (sorted) =
                             [(31,(3,[128,155])),(33,(2,[131,142]))]

ghc-4.08 profiling:  henselLift  takes   52,   19  % of time 
                       and is called      1,   16  times
                     GC  takes           25,   84  % of what?
                     total alloc =      116, 7339  Mb                
--------------------------------------------------------------------
f = f2
g = f4 
lengths of factors and monomial sums (sorted) =
                             [(33,(2,[131,142])),(38,(4,[170,179]))]

ghc-4.08 profiling:  henselLift  takes    40,   19  % of time 
                       and is called      17,    8  times
                     GC  takes            84,   60  % of what?
                     total alloc =     13663, 1023  Mb                
---------------------------------------------------------------------
f = f3
g = f4 
lengths of factors and monomial sums (sorted) =
                             [(31,(3,[128,155])),(38,(4,[170,179]))]

ghc-4.08 profiling:  henselLift  takes   16,   18  % of time 
                       and is called      5,   14  times
                     GC  takes           70,   76  % of what?
                     total alloc =     1568, 3905  Mb                



randRandFactor 10 **************************************************

f = f1 = 
  x^10*y^10 + 2*x^10*y^8 + 3*x^10*y^3 + 4*x^9*y^7 + 2*x^9*y + 3*x^9 
   + 4*x^8*y^10 + 3*x^8*y^8 + x^8*y^2 + 2*x^8 + 3*x^7*y^10 
   + 3*x^6*y^7 + x^6*y^6 + 3*x^5*y^9 + x^5*y^8 + x^4*y^9 + 3*x^4*y^8 
   + 4*x^4 + 4*x^3*y^2 + x^3 + 4*x^2*y^3 + x^2*y^2 + x^2*y + x^2 
   + x + 3*y^6 + y^4 + y^2 + y + 1 

g = f2 =
  x^10*y^9 + 3*x^10*y^7 + x^9*y^8 + 3*x^9*y^6 + 2*x^8*y^3 
   + 3*x^7*y^10 + x^7*y^7 + 4*x^7 + 4*x^6*y + 4*x^6 + 3*x^5 
   + x^4*y^6 + 4*x^4*y^5 + 3*x^3*y^6 + 4*x^3*y^5 + 2*x^2*y^8 
   + 2*x^2*y^7 + x*y^10 + 4*x*y^9 + 4*x + 4*y^10 + 2*y^8 + 3*y^3 
   + 4*y^2 + 3*y

lengths of factors and monomial sums (sorted) =
                             [(25,(0,[105,131])),(30,(4,[127,145]))]
                            
ghc-4.08 profiling:  henselLift  takes   17     52  % of time 
                       and is called     16     19  times
                     GC  takes           95     95  % of what?
                     total alloc =     6068, 12744  Mb                
--------------------------------------------------------------------
f = f1 
g = f3 =
  x^10*y^10 + 2*x^10*y^9 + 2*x^10*y^8 + x^9*y^7 + x^9*y^5 + x^9*y^4 
   + 4*x^9*y^2 + 4*x^8 + x^7*y^5 + 3*x^7*y^4 + 2*x^6*y^2 + x^6*y 
   + x^6 + 3*x^5*y^3 + 3*x^5*y^2 + x^4 + 2*x^3*y^9 + x^3*y^8 + 4*x^3 
   + 3*x^2*y^10 + x^2*y^2 + 3*x*y^2 + 2*x*y + 3*y^6 + 3*y^3 + 4*y^2 
   + 3*y + 4

lengths of factors and monomial sums (sorted) =
                             [(28,(4,[106,135])),(30,(4,[127,145]))]

ghc-4.08 profiling:  henselLift  takes   40,    52  % of time 
                       and is called     10,    17  times
                     GC  takes           89,   100  % of what?
                     total alloc =     7052, 11953  Mb 
--------------------------------------------------------------------
f = f1 
g = f4 =
  x^10*y^10 + 4*x^10*y^9 + 4*x^10*y^8 + 4*x^10*y^2 + x^10*y 
   + 3*x^9*y^10 + 2*x^9*y^5 + 2*x^9*y^3 + 3*x^9 + 3*x^8*y^5 
   + x^8*y^4 + 3*x^8*y^3 + 4*x^7*y^5 + 2*x^7*y^4 + 2*x^6*y^3 
   + 2*x^6*y^2 + x^6 + 3*x^5 + x^4*y^6 + 3*x^4*y^5 + x^3*y^4 
   + 2*x^3*y^2 + x^2*y^9 + 3*x^2 + 4*x*y^10 + 4*x + 4*y^10 + 2*y^9 
   + 4*y^3 + 3*y^2 + y + 1

lengths of factors and monomial sums (sorted) =
                             [(30,(4,[127,145])),(32,(4,[135,167]))]

ghc-4.08 profiling:  henselLift  takes   18,    53  % of time 
                       and is called     17,    10  times
                     GC  takes           82,    88  % of what?
                     total alloc =     8261, 11367  Mb
--------------------------------------------------------------------
f = f1 
g = f5 =
  x^10*y^9 + 4*x^10*y^8 + 4*x^10*y^3 + 3*x^10 + x^9*y^10 + 3*x^9*y^9 
   + x^9*y^4 + 3*x^9*y^3 + 4*x^8*y^7 + 3*x^8*y^5 + 3*x^8 + x^7*y^9 
   + 2*x^7*y^8 + 3*x^7*y^6 + 4*x^6*y^10 + 3*x^6*y^9 + 2*x^6*y^8 
   + 2*x^6*y^7 + 2*x^6 + x^5*y^8 + x^4*y^10 + 3*x^4 + 4*x^3*y^10 
   + 3*x^3*y^9 + x^3*y^8 + 2*x^3 + 3*x^2*y^10 + 2*x^2 + 2*x*y^10 
   + 2*x*y^9 + 3*x + y^10 + y^5 + y^4 + y^3 + y^2 + 4*y
--------------------------------------------------------------------
f = f2
g = f3
lengths of factors and monomial sums (sorted) =
                             [(25,(0,[105,131])),(28,(4,[106,135]))]

ghc-4.08 profiling:  henselLift  takes  27,   15  % of time 
                       and is called     3,    5  times
                     GC  takes          62,   74  % of what?
                     total alloc =     825, 2280  Mb
--------------------------------------------------------------------
f = f2
g = f4
lengths of factors and monomial sums (sorted) =
                             [(25,(0,[105,131])),(32,(4,[135,167]))]

ghc-4.08 profiling:  henselLift  takes    53,  40  % of time 
                       and is called      10,   3  times
                     GC  takes            89,  52  % of what?
                     total alloc =     11377, 467  Mb            
--------------------------------------------------------------------
f = f3
g = f4
lengths of factors and monomial sums (sorted) =
                             [(28,(4,[106,135])),(32,(4,[135,167]))]

ghc-4.08 profiling:  henselLift  takes   37,    53  % of time 
                       and is called     11,    13  times
                     GC  takes           58,    89  % of what?
                     total alloc =     1657, 11420  Mb 
--------------------------------------------------------------------




********************************************************************
********************************************************************
                      Family 1  of Examples

q = 5
p = t + 1
m = 6


********************************************************************
n = 5

DoCon-2-pre, SmallR, ghc-4.01    87 sec/factorization. 
March 1999, ghc-4.02             49
                      -Onot      73

(y^5 + (t^5 + 1)*y^4 + (2*t^2 + 2*t)*y^3 + (t + 1)) ^ 2 
(multiple prime)

MuPAD-1.3: 10 sec.

     4    5        3      2  3    5  4
t + y  + y  + 2 t y  + 2 t  y  + t  y  + 1,  2

---------------------
(y^5 + (t^5 + 1)*y^4 + (2*t^2 + 2*t)*y^3 + t + 1)
*
(y^5 + (t^5+1)*y^4 + (3*t^2+3*t)*y^3 + (t^3+3*t^2+3*t+1)*y + 2*t+2) 
(2 different primes)

MuPAD-1.3:  26 sec.

     4    5        3      2  3    5  4
t + y  + y  + 2 t y  + 2 t  y  + t  y  + 1,

                   4    5      2          3    3        2  3
2 t + y - 2 t y + y  + y  - 2 t  y - 2 t y  + t  y - 2 t  y  +

    5  4
   t  y  + 2
 
----------------------
(y^5 + (t^5 + 1)*y^4 + (2*t^2 + 2*t)*y^3 + t + 1) 
*
(y^5 + (t^5+1)*y^4 + (4*t^2+4*t)*y^3 + (2*t^3+t^2+t+2)*y + 3*t+3)
(2 different primes)

MuPAD-1.3: 27 sec
                     4    5    2        3      3      2  3    5  4
- 2 t + 2 y + t y + y  + y  + t  y - t y  + 2 t  y - t  y  + t  y  - 2
,
     4    5        3      2  3    5  4
t + y  + y  + 2 t y  + 2 t  y  + t  y  + 1


-------------------
(y^5 + (t^5 + 1)*y^4 + (2*t^2 + 2*t)*y^3 + t + 1) 
*
(y^5 + (t^5 + 1)*y^4 + (3*t^3 + 4*t^2 + 4*t + 3)*y + 4*t + 4) 
(2 different primes)



-------------------
(y^5 + (t^5+1)*y^4+(3*t^2+3*t)*y^3+(t^3+3*t^2+3*t+1)*y + 2*t + 2) 
*
(y^5 + (t^5 + 1)*y^4 + (2*t^2 + 2*t)*y^3 + t + 1) 
(2 different primes)


------------------
(y^5 + (t^5+1)*y^4 + (3*t^2+3*t)*y^3 + (t^3+3*t^2+3*t+1)*y + 2*t+2) ^2
(multiple prime)


**********************************************************************
n = 6

DoCon-2-pre, SmallR, ghc-4.01   130 sec/factorization
  March 1999,  ghc-4.02  -O      52

(y^6 + (t^6 + t^5 + t + 1)*y^5 + (2*t^2 + 2*t)*y^4 + t + 1) ^ 2
(multiple prime)

MuPAD-1.3:  9 sec

     5    6        4      5      2  4    5  5    6  5
t + y  + y  + 2 t y  + t y  + 2 t  y  + t  y  + t  y  + 1,    2



---------------------
(y^6 + (t^6 + t^5 + t + 1)*y^5 + (2*t^2 + 2*t)*y^4 + t + 1) 
*
(y^6 + (t^6+t^5+t+1)*y^5 + (3*t^2+3*t)*y^4 + (t^3+3*t^2+3*t+1)*y + 
                                                                 2*t+2
)
(2 different primes)

MuPAD-1.3:  69 sec

     5    6        4      5      2  4    5  5    6  5
t + y  + y  + 2 t y  + t y  + 2 t  y  + t  y  + t  y  + 1, 

                   5    6      2      3          4
2 t + y - 2 t y + y  + y  - 2 t  y + t  y - 2 t y  +

      5      2  4    5  5    6  5
   t y  - 2 t  y  + t  y  + t  y  + 2


---------------------
(y^6 + (t^6 + t^5 + t + 1)*y^5 + (2*t^2 + 2*t)*y^4 + t + 1) 
*
(y^6 + (t^6+t^5+t+1)*y^5 + (4*t^2+4*t)*y^4 + (2*t^3+t^2+t+2)*y +3*t+3)
(2 different primes)

MuPAD-1.3:  52 sec
                     5    6    2        3        4      5    2  4
- 2 t + 2 y + t y + y  + y  + t  y + 2 t  y - t y  + t y  - t  y

      5  5    6  5
   + t  y  + t  y  - 2, 

     5    6        4      5      2  4    5  5    6  5
t + y  + y  + 2 t y  + t y  + 2 t  y  + t  y  + t  y  + 1, [y, t],




********************************************************************
n = 7

DoCon-2-pre, SmallR, ghc-4.01             sec/factorization
  March 1999,  ghc-4.02       
                        -O    75 

(y^7 + y^6*t^7 + 2*y^6*t^6 + y^6*t^5 + y^6*t^2 + 2*y^6*t + y^6 
  + 2*y^5*t^2 + 2*y^5*t + t + 1
)^ 2


--------------------------------------------------------------------
(y^7 + y^6*t^7 + 2*y^6*t^6 + y^6*t^5 + y^6*t^2 + 2*y^6*t + y^6 
  + 2*y^5*t^2 + 2*y^5*t + t + 1
) *
(y^7 + y^6*t^7 + 2*y^6*t^6 + y^6*t^5 + y^6*t^2 + 2*y^6*t + y^6 
  + 3*y^5*t^2 + 3*y^5*t + y*t^3 + 3*y*t^2 + 3*y*t + y + 2*t + 2
)

--------------------------------------------------------------------
(y^7 + y^6*t^7 + 2*y^6*t^6 + y^6*t^5 + y^6*t^2 + 2*y^6*t + y^6 
  + 2*y^5*t^2 + 2*y^5*t + t + 1
) *
(y^7 + y^6*t^7 + 2*y^6*t^6 + y^6*t^5 + y^6*t^2 + 2*y^6*t + y^6 
  + 4*y^5*t^2 + 4*y^5*t + 2*y*t^3 + y*t^2 + y*t + 2*y + 3*t + 3
)



--------------------------------------------------------------------
(y^7 + y^6*t^7 + 2*y^6*t^6 + y^6*t^5 + y^6*t^2 + 2*y^6*t + y^6 
  + 2*y^5*t^2 + 2*y^5*t + t + 1
) *
(y^7 + y^6*t^7 + 2*y^6*t^6 + y^6*t^5 + y^6*t^2 + 2*y^6*t + y^6 
  + 3*y*t^3 + 4*y*t^2 + 4*y*t + 3*y + 4*t + 4
) 


--------------------------------------------------------------------
(y^7 + y^6*t^7 + 2*y^6*t^6 + y^6*t^5 + y^6*t^2 + 2*y^6*t + y^6 
  + 3*y^5*t^2 + 3*y^5*t + y*t^3 + 3*y*t^2 + 3*y*t + y + 2*t + 2
) *
(y^7 + y^6*t^7 + 2*y^6*t^6 + y^6*t^5 + y^6*t^2 + 2*y^6*t + y^6 
  + 2*y^5*t^2 + 2*y^5*t + t + 1
)

--------------------------------------------------------------------
(y^7 + y^6*t^7 + 2*y^6*t^6 + y^6*t^5 + y^6*t^2 + 2*y^6*t + y^6 
  + 3*y^5*t^2 + 3*y^5*t + y*t^3 + 3*y*t^2 + 3*y*t + y + 2*t + 2
) *
(y^7 + y^6*t^7 + 2*y^6*t^6 + y^6*t^5 + y^6*t^2 + 2*y^6*t + y^6 
  + 3*y^5*t^2 + 3*y^5*t + y*t^3 + 3*y*t^2 + 3*y*t + y + 2*t + 2
) 

-}




















