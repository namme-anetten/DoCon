-- DoCon-2.12  Demonstration, test, benchmark.



module T_primes (primesBySieve, t_primes_)
where
-- generating prime integers, factoring integer

import DPrelude   (Natural, factorial)
import RingModule (FactorizationRing(..))
import Z          ({- FactorizationRing Z -})




------------------------------------------------------------------------
primesBySieve :: [Natural]        
                       -- Infinite list of primes produced by the sieve.
                       -- Nice but too expensive for the large numbers.
                       -- There are known much less expensive methods.
primesBySieve = sieve [2 ..]  
                where 
                sieve (p: ns) = p: (sieve [n | n <- ns, (mod n p) /= 0])

t_primes_ =     
  ((sieveTestSmall, sieveTest), (test, test'), (fts, primaries, fts'))
  where
  pn             = primesBySieve !! 1001 
  pn'            = primesBySieve !! 300
  sieveTest      = pn == 7933               
  sieveTestSmall = pn' == 1993
  ns = [7^9, 7^9*3^2, 11^11, 11^11*3, 11^11*3^11, 73313783*31*11,
                                                  factorial 50]
                                                            :: [Natural]
  fts       = zip ns $ map factor ns
  primaries = filter isPrimary ns
  isPrimary = (== 1) . length . factor     -- example: 3^4 <--> [(3, 4)]
  smallPrimeBound = 25*10^9 - 1  :: Natural

  fts' = map factor [smallPrimeBound .. (smallPrimeBound + 6)] 
                                -- expensive in DoCon-2, though feasible
  ftsCheck = [[(7,9)],  [(7,9),(3,2)],  [(11,11)],[(11,11),(3,1)],
              [(11,11),(3,11)],  [(73313783,1),(31,1),(11,1)],
              [(47,1),(43,1),(41,1),(37,1),(31,1),(29,1),(23,2),
               (19,2),(17,2),(13,3),(11,4),(7,8),(5,12),(3,22),(2,47)]
             ]
  fts'Check = [[(85733,1),(7477,1),(13,1),(3,1)],[(5,11),(2,9)],
               [(1422637,1),(17573,1)],[(462962963,1),(3,3),(2,1)],
               [(73313783,1),(31,1),(11,1)],[(892857143,1),(7,1),(2,2)],
               [(1666666667,1),(5,1),(3,1)]
              ]
  primrCheck = [40353607, 285311670611]
  test  =  (map snd fts) == ftsCheck  &&  primaries == primrCheck
  test' =  fts' == fts'Check


-- Test.     See  Test.hs
--------



-- Benchmark
------------
-- s'  where  ((s, s'), (t, t'), _) = t_primes_
--
-- - switch here between  s, s', t, t'  and see the timing.


-- Further demonstration
------------------------
-- print other parts of
-- let  (_, _, (fts, primaries, fts')) = t_primes_  in ..





{- Timing ----------------------------------------------------------


August 1999. i586 166MHz, ghc-4.04, DoCon-2, -O     
                      sieveTest(1001) 
                                      :: Int      -M50k -K4  1.0 sec
                                      :: Integer  ...        1.5

Hugs-98-990319,  9Mbyte    
                          sieveTest(1001)
                                      16Mbyte    40.0
                                           ghc/hugs speed = 37  (!?)

                                  show test                   test'
                                        1.00                 1700.0
       
                                                  ghc/hugs = 18 (?!)
--------------------------------------------------------------------
-}





{- Demo 2 ----------------------------------------------------------

Note on "lazy" lists.

  let {ps = primesBySieve;  n = 1000}
  in
  ps !! (n+1)                                -- (P1)
  (ps !! n, ps !! (n+1))                     -- (P2)
  (ps !! n, ps !! (n+1), ps !! (quot n 2))   -- (P3)


This is how primesBySieve works:

2: (filter ((/= 0). mod 2) (ps [3 ..]))

2: (filter ((/= 0). mod 2) 
     (3: (filter ((/= 0) . mod 3)) (ps [4 ..))))
    )
2:3: (filter ((/= 0) . mod 3) (ps [4 ..)))
...
How much differ in the running cost the variants (P1),(P2),(P3) ?
They do not differ any essentially.

Thus, with  ghc-2.10-linux,  ghc -c -O Main.hs  compilation,  
it takes the same time (+- 1%)  for (P1),(P2),(P3).

(P1):  7933                -- p(n+1)             
(P2):  (7927, 7933)        -- p(n),p(n+1)        
(P3):  (7927, 7933, 3581)  -- p(n),p(n+1),p(n/2) 

This is because the (!!) function invocates not more than 3 times,
and this costs much cheaper than the whole program.
On the second, the first (n+1) values in primes'  needed in (P2) for
the first component of the pair also participate in the evaluation 
of the second component. The interpreter reuses these values.

DoCon assumes the programming style in which  the  expressions  like
(P2),(P3) may well appear.
-}












