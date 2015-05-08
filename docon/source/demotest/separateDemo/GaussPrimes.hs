-- DoCon-2.12  Demonstration, test, benchmark.                            
-- Finding Prime Elements in the Gaussian Integer Ring               
-- G = Integer[i] / I(i^2 + 1).                                           

-- Installation.                                                             
-- 1. Install the Glasgow Haskell tool  ghc-7.4.1.                           
-- 2. Install DoCon-2.12  (see its  install.txt).                            
-- 3. Set the environment variable  $doconCpOpt  as requred in                
--                                                          install.txt.     
-- 4. Build:                                                                  
--           ghc $doconCpOpt -O -rtsopts --make GaussPrimes                  
-- 5. Run:   time ./GaussPrimes > log                                        
--                                                                           
--    It prints the result to the file  ./log                                
--                                                                           
-- 6. Setting the argument value for `bound':                                
--    set it before compilation in the function  main = ...                   
--                                                      where                 
--                                                      bound = ...           
-- Attached print outs:                                              
--   log96.txt    for  bound =   96     38893 b,       
--   log200.txt   for  bound =  200    165313 b,        2   sec
--   logg400.txt  for  bound =  400    615673 b,       18   sec
--                                          blade:      1.4 sec
--   log2000.txt  for  bound = 2000   13944013 b,     
--                                          blade:    100 sec


module Main
where
import Data.List   (find)    -- of Haskell library
import Debug.Trace (trace)   -- of GHC ?

-- of DoCon --------------------------                                        
import DPrelude   (Natural, Comparison, sortBy, lexListComp)
import SetGroup   (squareRootOfNatural, divides)
import RingModule (FactorizationRing(..))
import Z          ()  -- FactorizationRing Integer
-------------------------------------                                       
  



------------------------------------------------------------------------ 
-- Definition:
-- I-Gaussian  is a gaussian x + y*i  of the first Quadrant:  x, y >= 0.       
-- 8-Gaussian  is a Gaussian of the first          Octant:  x >= y >= 0.     
-- 8-prime     is a prime 8-Gaussian.                                        
  
swap :: (a, b) -> (b, a)   -- where it is in the library? **                
swap    (a, b) =  (b, a)

type NN = (Natural, Natural)
type ZZ = (Integer, Integer)

sqRoot_lower         = squareRootOfNatural 
sqRoot_upper x bound = succ $ sqRoot_lower x bound

lexPairComp :: Ord a => Comparison (a, a)
lexPairComp (x, y) (x', y') = lexListComp compare [y, x] [y', x']          

------------------------------------------------------------------------ 
toSquareSum2 :: Natural -> [NN]
                -- all different decompositions  n = k^2 + m^2,  k >= m      
toSquareSum2 0 =  [(0, 0)] 
toSquareSum2 n =  [(m, k) | (k, n', m) <- triples, k <= m, m^2 == n']
        where
        -- n > 1
        sucHalf_n = succ $ quot n 2
        r         = sqRoot_upper sucHalf_n sucHalf_n
        pairs     = takeWhile (\ (_, n') -> n' >= 0)
                                          [(k, n - k^2) | k <- [1 .. r]]
                                            -- (0, n) is prepended later 
        r0      = sqRoot_lower n n
        triples = (0, n, r0) : (addRoots r0 pairs)
        addRoots _        []                = []
        addRoots lastRoot ((k, n') : pairs) = 
                         let newRoot = sqRoot_lower n' (succ lastRoot)
                         in  (k, n', newRoot) : (addRoots newRoot pairs)
          
nextNorm :: Natural -> (Natural, NN)
nextNorm nr = (nr', pair)
              where
              Just (nr', pair: _) = 
                     find (not . null . snd)
                          [(nr, toSquareSum2 nr) | nr <- [(succ nr) ..]]
                                                     
ofNorm :: NN -> [NN]
ofNorm (a, b) = toSquareSum2 (a^2 + b^2)
                       -- all 8-gaussians (x, y) of norm  nr = a^2 + b^2     
-- It applies  sqRoot_upper  root(a^2 + b^2)  times.
-- Probably, it is faster to appriximate the circumference by integer 
-- unit squares.

norm2 :: (Integer, Integer) -> Natural
norm2 (x, y) =  x^2 + y^2 

------------------------------------------------------------------------ 
-- Prime Gaussians are these and only these elements.
-- 1) +-q, +-q*i,  where  q  is a prime natural of kind  4*m - 1,    
--                                              m  a positive natural. 
-- 2) +- (1 +-i)   (of norm 2).
-- 3) s = a + b*i,   norm(s)  a prime number of kind  4*l + 1,  
--                                                    l integer.
-- It holds a partition
--          8-Gauss primes =  realGaussPrimes U gaussPrimeOfNorm2 U
--                                              nontrivialGaussPrimes 
-- -- for the functions defined below:

gaussPrimeOfNorm2 :: NN                    -- a single 8-prime of norm 2
gaussPrimeOfNorm2 =  (1, 1)

realGaussPrimes :: [NN]                                 -- only 8-primes
realGaussPrimes =  [(q, 0) | m <- [1 ..], let q = 4*m - 1, isPrime q]    
               
nontrivialGaussPrimes :: [(Natural, [NN])]  -- 8-primes gathered by norm
nontrivialGaussPrimes = 
  [(q, sortBy lexPairComp gs) | l <- [1 ..], let q = 4*l + 1, isPrime q,
                                let gs = toSquareSum2 q,  not $ null gs] 
  
------------------------------------------------------------------------  
gaussPrimeList :: Natural -> [ZZ]                                          
                  -- bound                                                    
-- Required by S. Duzhin.                                                     
-- It uses  gaussPrimes  to build the table for primes in the square          
--                                    [-bound, bound] x [-bound, bound].      
-- The result is ordered lexicographically by  [y, x].                        
-- Method:  build  Sieve for  the Octant,  add symmetrics,  sort.             
                                                                              
gaussPrimeList bound =  sortBy lexPairComp $  
                        concat [ primes_4,                                    
                                 [(-x,  y) | (x, y) <- primes_4],             
                                 [(-x, -y) | (x, y) <- primes_4],             
                                 [(x,  -y) | (x, y) <- primes_4] ]            
  where                  
  normBound        =  succ (2*bound^2)           
  isInBound (x, y) =  x <= bound && y <= bound
  realsB    = takeWhile isInBound realGaussPrimes
  nonTrivsB = let nts = takeWhile ((normBound >=) . fst)
                                              nontrivialGaussPrimes
              in  concat [filter isInBound gs | (_, gs) <- nts] 
              
  primes_8 = gaussPrimeOfNorm2 : (realsB ++ nonTrivsB)
  primes_4 = primes_8 ++ (map swap primes_8)
  

showsZZList :: [ZZ] -> String -> String     -- the printing format            
showsZZList pairs = case pairs              -- required by S.Duzhin           
                    of                                                        
                    []          -> id                                         
                    (m, n) : ps -> shows m . showChar ' ' . shows n .         
                                   showChar '\n' . showsZZList ps             

 
nonSingletonGaussPrimeLevel :: (Natural, [NN])  
                                             -- find any of length > 1 !
nonSingletonGaussPrimeLevel =  
          findLargeLevel $ zip [(1 :: Natural) ..] nontrivialGaussPrimes 
   where
   bnd = 4*10^6
   findLargeLevel ((i, (nr, gs)) : levels) =

         if length gs > 1 then (nr, gs)
         else
         (if  nr > bnd && divides 5000 i  then
                                trace ("norm = " ++ (shows nr "  done"))
          else  id
         ) $          
         findLargeLevel levels

   findLargeLevel _ = error "\nfindLargeLevel []\n"


main = putStr $ shows nonSingletonGaussPrimeLevel "\n"

-- main = putStr $ showsZZList (gaussPrimeList bound) "\n"  where             
   --                                                      bound = 2000
  -- Required by S. Duzhin.                                                   
  -- Prints in one column a great number of prime Gaussians. 

