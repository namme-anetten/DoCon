------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------





module ResEuc0_  -- Several initial items for the residue ring Z/(b) and
                 -- residue of a generic Euclidean ring.
                 -- All needed from here is  reexported by  Residue.
(Residue(..),
 resSubgroup, resSSDom, resIdeal, resIIDom,  isCorrectRse, ifCorrectRse
 -- , instances for class Residue:          Show, DShow, Eq
 --                 constructor  ResidueE:  Dom, Cast, Residue
)
where
import DPrelude (DShow(..), Cast(..)) -- classes
import Categs   (Dom(..), Domains1, Subgroup(..), PIRChinIdeal(..), 
                                                Ideal(..), ResidueE(..))
import Ring0_ (EuclideanRing(..))
import Ring1_ (remEuc)





------------------------------------------------------------------------
-- Several common items for the residue constructors
-- ResidueG, ResidueE, ResidueI

class Residue r  
  where  
  resRepr   :: r a -> a                        -- extract representation
  resPIdeal :: r a -> PIRChinIdeal a
                      -- ideal of quotientation - case of Euclidean ring

  resGDom :: r a -> (Subgroup a, Domains1 a)   
     -- 
     -- for the quotient group  a/gH.
     -- Returns (gH,dH),  gH a normal subgroup of quotientation, 
     --                   dH domain bundle for gH (contains gH too).

  resIDom :: r a -> (Ideal a, Domains1 a) 
                                        -- for generic residue ring case

  -- Each of the last three operations either has to be skipped or to 
  -- yield the error break when applied to the residue of improper kind. 


resSubgroup :: Residue r => r a -> Subgroup a
resSubgroup =  fst . resGDom

resSSDom :: Residue r => r a -> Domains1 a
resSSDom =  snd . resGDom

resIdeal :: Residue r => r a -> Ideal a
resIdeal =  fst . resIDom

resIIDom :: Residue r => r a -> Domains1 a
resIIDom =  snd . resIDom

instance (Residue r, Show a) => Show (r a) where 
                                           showsPrec _ = shows . resRepr
instance (Residue r, DShow a) => DShow (r a) where
                                       dShows opt = dShows opt . resRepr
instance (Residue r, Eq a) => Eq (r a) 
  where
  x == y =  (resRepr x) == (resRepr y)
                       -- this relies on that  x  is canonically reduced


------------------------------------------------------------------------
instance EuclideanRing a => Cast (ResidueE a) a
  where
  cast 'r' (Rse _ iI d) a = Rse (remEuc 'c' a $ pirCIBase iI) iI d
  cast _   (Rse _ iI d) a = Rse a iI d


instance Residue ResidueE
  where  
  resRepr   (Rse x _  _) = x
  resPIdeal (Rse _ iI _) = iI
  resGDom   _         = error "resGDom (Rse..)  - not defined for Rse\n"
  resIDom   _         = error "resIDom (Rse..)  - not defined for Rse\n"

instance Dom ResidueE where  dom (Rse _ _ d) = d
                             sample          = resRepr

isCorrectRse :: EuclideanRing a => ResidueE a -> Bool
isCorrectRse (Rse x i _) =  x == (remEuc 'c' x $ pirCIBase i)

-- specialize isCorrectRse :: ResidueE Z -> Bool #-

ifCorrectRse x y z = if  isCorrectRse x  then z  else y



{- reserve *************************
instance (Convertible a b, EuclideanRing b) => 
                                              Convertible a (ResidueE b)
  where  cvm a r = fmap (ctr r) (cvm a (resRepr r))
******************
-}
