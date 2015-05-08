------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2008
------------------------------------------------------------------------
------------------------------------------------------------------------





module Residue 

  -- Quotient group  and  Residue ring  constructors. 
  --
  -- This head module only reexports the needed items.
  -- See  QuotGr_, IdealSyz_, ResEuc0_ ...

  (ResidueE(..),   -- from Categs

   module QuotGr_,
   -- ResidueG(..), isCorrectRsg,                
   -- instances  Show,Eq,Cast, Residue, Dom, Random, Set .. AddGroup
   
   gensToIdeal,   -- from IdealSyz_

   module ResEuc0_,
   -- class Residue(..), 
   -- resSubgroup, resSSDom, resIdeal, resIIDom, isCorrectRse,
   -- ifCorrectRse,
   -- instances for Residue class:          Show, Eq,
   --           for constructor  ResidueE:  Dom, Cast, Residue
 
   module ResEuc_,
   -- instances for  ResidueE:
   -- Random, Set, AddSemigroup, AddMonoid, AddGroup, MulSemigroup, 
   -- MulMonoid, Ring, CommutativeRing, LinSolvRing, GCDRing, 
   -- FactorizationRing, EuclideanRing, Field, 
   -- specialization for  ResidueE Z  for the instances  
   --   Set, AddSemigroup, AddGroup, MulSemigroup, Ring

   module RsePol_,
   -- specialization of  ResidueE  to  Field k => ResidueE (UPol k):
   -- instances up to  Ring,  maxDimMonSubAlgInRseUPolRseUPol

   module ResRing_,
   -- ResidueI(..), isCorrectRsi,
   -- instances for  .. => ResidueI a: 
   --                    Dom, Residue, Cast, Set .. Num, Fractional
  )
where
import Categs (ResidueE(..))
import QuotGr_   
import IdealSyz_ (gensToIdeal)
import ResEuc0_
import ResEuc_
import RsePol_   (maxDimMonSubAlgInRseUPolRseUPol)
import ResRing_  hiding (fromexpr_)
import ResRing__ ()   -- continuation:  instances  Ring .. Field
import ResPol_   ()
          -- instances Set,AddSemigroup,Ring  for  ..=> ResidueI (Pol a)
