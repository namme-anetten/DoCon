------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------




module PP_   -- Operations on Power Products.
             -- See  Manual `pol.pp',  Pol.hs.
             -- All needed from here is  reexported by  Pol.

(isMonicPP, ppLcm, ppComplement, vecMax, ppMutPrime, ppDivides, 
 lexComp, lexFromEnd, degLex, degRevLex, ppComp_blockwise, 

 PowerProduct, PPComp   -- from Categs
)
where
import Data.List (genericSplitAt) 
import DPrelude  (Length(..), -- class 
                  Natural, CompValue,  lexListComp)
import Categs    (PowerProduct, PPComp)
import SetGroup  (AddMonoid(), zeroS)
import VecMatr   (Vector(..), vecRepr, vecHead)
import Z         ()




------------------------------------------------------------------------
-- imported:  type PowerProduct = Vector Integer
--            type PPComp       = Comparison PowerProduct
  
                  
isMonicPP :: PowerProduct -> Bool 
                                -- "depends not more than on 1 variable"
isMonicPP =  (< 2) . genLength . filter (/= 0) . vecRepr

vecMax, ppLcm ::  Ord a => Vector a -> Vector a -> Vector a

vecMax v = Vec . zipWith max (vecRepr v) . vecRepr
                            
ppLcm = vecMax               -- Least Common Multiple of power products

{-# specialize 
    vecMax :: Vector Integer -> Vector Integer -> Vector Integer #-}

ppComplement :: PowerProduct -> PowerProduct -> PowerProduct
ppComplement    u               v            =  (ppLcm u v) - u

vecMutPrime :: AddMonoid a => Vector a -> Vector a -> Bool
vecMutPrime v =  
         and . zipWith (\ x y -> x == z || y == z) (vecRepr v) . vecRepr
                                                   where
                                                   z = zeroS $ vecHead v
{-# specialize 
    vecMutPrime :: Vector Integer -> Vector Integer -> Bool #-}


ppMutPrime :: PowerProduct -> PowerProduct -> Bool
ppMutPrime =  vecMutPrime         -- "power products are Mutually Prime"

ppDivides :: PowerProduct -> PowerProduct -> Bool
ppDivides p q =  all (>= 0) $ vecRepr (q - p)           -- "p divides q"



------------------------------------------------------------------------
-- Some usable admissible comparisons for power products ***********

lexComp :: PPComp 
lexComp v =  lexListComp compare (vecRepr v) . vecRepr

lexFromEnd :: PPComp 
lexFromEnd v = 
           lexListComp compare (reverse $ vecRepr v) . reverse . vecRepr

degLex :: PPComp 
degLex p@(Vec ns) q@(Vec ms) = case compare (sum ns) (sum ms) of
                                                       EQ -> lexComp p q
                                                       v  -> v
degRevLex :: PPComp 
degRevLex p@(Vec ns) q@(Vec ms) = case compare (sum ns) (sum ms) of
                                                    EQ -> lexFromEnd q p
                                                    v  -> v
  -- Mind degRevLex!  It is not so trivial.  For example, for  n = 3
  -- it is presented by the matrix [u1,-e3,-e2] = [[1, 1, 1],
  --                                               [0, 0,-1],
  --                                               [0,-1, 0]
  --                                              ]


------------------------------------------------------------------------
ppComp_blockwise :: 
     Natural-> PPComp-> PPComp-> PowerProduct-> PowerProduct-> CompValue
     -- m      cp       cp'      p              q  
-- compare p q  by the direct sum of comparisons cp, cp':
-- first  cp  compares the vectors of the first  m  items from  p,q,
-- then, if equal, the rest are compared by  cp'.

ppComp_blockwise m cp cp' (Vec js) (Vec ks) =
  let
     (js', js'') = genericSplitAt m js
     (ks', ks'') = genericSplitAt m ks
  in
  case  cp (Vec js') (Vec ks')  of  EQ -> cp' (Vec js'') (Vec ks'')
                                    v  -> v
