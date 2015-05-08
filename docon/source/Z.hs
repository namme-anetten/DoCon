--------------------------------------------------------------------
--------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2007
--------------------------------------------------------------------
--------------------------------------------------------------------




module Z    -- Category instances for  Z = Integer.

  (dZ, 

   -- from SetGroup
   orderModuloNatural, totient, rootOfNatural, minRootOfNatural
   -- , instances for Integer: 
   -- Set, OrderedSet, AddSemigroup, OrderedAddSemigroup, AddMonoid,
   -- OrderedAddMonoid, MulSemigroup, MulMonoid, AddGroup, 
   -- OrderedAddGroup
   
   -- from Ring_
   -- instances for Integer:
   -- Fractional, Ring, CommutativeRing, OrderedRing,

   -- from Ring1_
   -- instances for Integer:  LinSolvRing, EuclideanRing
  )
where

import qualified Data.Map as Map (empty, lookup, insert)

import DPrelude (PropValue(..), Z)
import Categs    
       (CategoryName(..), Domain1(..), Domains1, FactrRingTerm(..), 
        Property_FactrRing(..), Factorization
       )
import SetGroup (orderModuloNatural, totient, rootOfNatural, 
                 minRootOfNatural
                )
import Ring0_ (FactorizationRing(..), upEucFactrRing)
import Ring1_ ()
import Ring1_ (multiplicity)





------------------------------------------------------------------------
dZ :: Domains1 Z
dZ =  upEucFactrRing 0 Map.empty


instance FactorizationRing Integer  
  where
  factor   = factor_
  isPrime  = isprime_
  primes _ = primes_

  baseFactrRing _ dm = 
    case  Map.lookup FactorizationRing dm  
    of
    Just (D1FactrR t) -> (dm, t)
    _                 -> 
                       (Map.insert FactorizationRing (D1FactrR t) dm, t)
      where
      t = FactrRingTerm {factrRingProps = 
                                 [(WithIsPrime, Yes), (WithFactor, Yes), 
                                  (WithPrimeList, Yes)]
                        }


------------------------------------------------------------------------
-- local

primes_ :: [Z]        -- Infinite list of all prime natural numbers.
                      -- 
                      -- After  smallPrimeBound,  it is very slow,  
primes_ =             -- but we will hardly ever reach this bound. 
  let
    sieve (p:ns)      = p: (filter ((/= 0) . (`rem` p)) (sieve ns))
    noDivsInList ps n =  
                  all ((/= 0) . rem n) (takeWhile (\ p -> p^2 <= n) ps)

    smallPrimes = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59]
                  ++
                  (filter isSmallPrime [61 .. smallPrimeBound])   
    larges = filter (noDivsInList smallPrimes) [(smallPrimeBound+2) ..]
  in
  smallPrimes ++ (sieve larges)


smallPrimeBound = 25*10^9 - 1  :: Z

------------------------------------------------------------------------
isSmallPrime :: Z -> Bool

  -- Primality testing for   10 < n <= smallPrimeBound
  --
  -- The method comes from  
  --   Pomerance C., Selfridge J.L., Wagstaff S.S.:
  --   The pseudoprimes to 25*10^9.
  --   Math.Comput., 1980, v.36, No.151, pp.1003-1026.


isSmallPrime x = 
  case  multiplicity 2 (x-1)  `asTypeOf` (x, x)  
  of
  (0, _) -> False                       -- n  is even
  (s, d) ->                             -- n-1 = d*2^s,  d is odd
            x /= 3215031751  &&
            all (isStrongPseudoPrimeByBase x d s) [2, 3, 5, 7]   
    where
    isStrongPseudoPrimeByBase x d s base =
      let
        bp       = powerMod x base d               -- (base^d) mod x
        bpPowers = map (powerMod x bp) (1 : [2^r | r <- [1 .. (s-1)]])
      in
      (rem (bp-1) x) == 0  ||
      any (\ m -> (rem (m+1) x) == 0) bpPowers

    powerMod x y d = pw d   -- (y^d) modulo x,  x,d > 0, y >= 0
                   where
                   y'   = rem y x
                   pw 1 = y'
                   pw 0 = rem 1 x
                   pw d = let  h = pw $ quot d 2
                          in
                          if  even d  then  rem (h*h) x
                          else              rem (y'*(rem (h*h) x)) x

------------------------------------------------------------------------
isprime_ :: Z -> Bool
isprime_ n = if n < 0 then  isprime_ (- n)
             else
             elem n [2, 3, 5, 7]
             ||
             (n > 10  &&
              if  n <= smallPrimeBound  then  isSmallPrime n
              else
              all ((/= 0) . rem n) (takeWhile ((n >=) . (^2)) primes_)
             )

------------------------------------------------------------------------
factor_ :: Z -> Factorization Z                -- see `factor' operation

factor_ 0 = error "factor (0 ::Z) \n"
factor_ 1 = []   
factor_ x = if x < 0 then  factor_ (-x)  else  f x primes_ []   
  where
  f 1 _       fts = fts
  f x (p: ps) fts = case (p^2 > x, isprime_ x, multiplicity p x)
                   of
                   (True, _   , _     ) -> (x, 1): fts
                   (_,    True, _     ) -> (x, 1): fts
                   (_,    _,    (0, _)) -> f x ps fts
                   (_,    _,    (m, q)) -> f q ps ((p, m): fts)
