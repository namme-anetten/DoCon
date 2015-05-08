module Main 
where
import qualified Data.Map as Map (empty)
import DExport 

-- Denote   
-- a  <-->  any Euclidean ring A,   AX = A[x]   <--> UPol a, 
--
-- R = A/(m),  as depending on  m <- A.   R <--> Residue a.
--
-- Denote  P = R[x].
--
-- For the given polynomials  f, g  from  A[x]  
-- find GCD for their projections to      (A/(m))[x]
-- for each  m <- ms,  m <- A
--
-- -- but first, DoCon must decide (automatically) which of these 
-- domains are correct for GCD.

projectPol :: (EuclideanRing a, FactorizationRing a) 
              => 
              a -> UPol a -> UPol (ResidueE a)
projectPol    m    f      =                    -- A[x] -> (A/(m))[x]
  let
    unA = unity m                    -- unity of  A
    dA  = upEucRing unA Map.empty    -- the domain  A
    iI  = eucIdeal "bef" m [] [] []
    r1  = Rse unA iI dA              -- 1 of R
    dR  = upField r1 Map.empty       -- the domain  R
    p1  = cToUPol "x" dR r1          -- 1  of  P = R[x]
  in
  ctr p1 [(ctr r1 a, e) | (a, e) <- upolMons f]

  -- ctr r a  
  -- projects  a <- A  to the domain of  r 
  -- (generally, this is casting between domains).
  -- In our case,  ctr r1 a              casts to  A/(m), 
  --               ctr p1 monomialList   casts to  P(m).


gcdMods :: (EuclideanRing a, FactorizationRing a) 
           => 
           UPol a -> UPol a -> [a] -> [UPol (ResidueE a)]
gcdMods    f         g         ms  =

                [ gcD [projectPol m f, projectPol m g]  |  m <- ms ] 



-- Example of using  gcdMods,  with  A = Integer  (<--> dZ) :

main =   
 let 
   unX = cToUPol "x" dZ (1 :: Integer)   :: UPol Integer
                             --
                             -- unity of AX, serves also as a sample

   f = smParse unX " (x^2 + 2*x + 3)*(3*x + 1) "
   g = smParse unX " (x^2 + 2*x + 3)*(x + 2)^3 "
                         --
                         -- parse value from string using unX as
                         -- a sample defining the destination domain

   ms = [2, 3, 5]  -- [6]

   gcs     = gcdMods f g ms
   lastRes = last gcs           -- look into the domain description
                                -- of the last result, for curiosity
   (_, setP ) = baseSet  lastRes Map.empty     --
   (_, ringP) = baseRing lastRes Map.empty  
 in
 putStr $ concat 
 ["\n",
  show gcs,                  "\n\n",
  show (osetCard setP),      "\n\n",
  show (subringProps ringP), "\n\n"
 ]
 -- For  ms = [2, 3, 5],
 -- it prints  [x^2 + 1,  x^2 + 2*x,  x^3 + 4*x^2 + 2*x + 1]
 --
 --            Infinity
 --
 --            [ (Field, No), (Factorial, Yes) ... ]
 -- 
 -- For  ms = [6],   it prints
 --
 --   baseGCDRing r dom',    r = 1  <- D/I =  (Z/<6>)
 -- 
 --   Prime iI needed