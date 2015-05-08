------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------





module Pol

  -- Polynomial constructors.
  --
  -- This head module reexports many items implemented in 
  -- PP_, Pol*_*, Pgcd_, EPol*_* ...

  (
   UMon, PowerProduct, PPComp,   -- from  Categs

   -- from PP_
   isMonicPP, ppLcm, ppComplement, vecMax, ppMutPrime, ppDivides, 
   lexComp, lexFromEnd, degLex, degRevLex, ppComp_blockwise,

   -- from UPol_
   PolLike(..), PolVar, Mon, UPol(..), PPOrdTerm, PPOId, 
   Multiindex, ppoId, ppoComp, ppoWeights, lexPPO, varP, deg0, lc0,
   pHeadVar, lc, cPMul, pCont, numOfPVars, upolMons, lmU, umonMul, 
   mUPolMul, umonLcm, leastUPolMon, cToUPol, upolPseudoRem, 
   monicUPols_overFin,
   -- instance (PolLike p...) => LeftModule a (p a),
   -- instances for UPol:        Dom, Eq, Cast, PolLike,

   -- from UPol0_
   resultant_1, resultant_1_euc, discriminant_1, discriminant_1_euc, 
   charMt, charPol, matrixDiscriminant,  upolSubst, upolInterpol,          
   -- , instances for UPol:
   --   Show, DShow, Set, AddSemigroup, AddMonoid, AddGroup, 
   --   MulSemigroup, MulMonoid, Num, Fractional, Ring, CommutativeRing

   -- from Pol_:
   Pol(..), PolPol, 
   polMons, cToPol, reordPol, leastMon, monMul, mPolMul, monLcm, 
   headVarPol, fromHeadVarPol, polToHomogForms, addVarsPol, toUPol, 
   fromUPol, coefsToPol, polDegs, polPermuteVars,
   -- instances for Pol:  Show, Eq, Dom, Cast, PolLike,

   PVecP, sPol, mPVecPMul, sPVecP,                    -- from  Pol__
   RPolVar, showsRPolVar, SPProduct, SPMon, SPPol', showsSPPol',

                                                          -- from  Pol1_
   PPCoefRelationMode(..), toPolOverPol, fromPolOverPol, polSubst, 
   polValueInCommRing, 
   -- instances for Pol:  Show, Set .. CommutativeRing,

   module Pol2_,
   -- toOverHeadVar, fromOverHeadVar, 
   -- LinSolvRing, EuclideanRing  instances for  UPol,
   -- LinSolvRing                                Pol,
   -- instance..=> LinSolvLModule (Pol  a) (EPol a),
   --              LinSolvLModule (Pol  a) (Vector (Pol  a)),
   --              LinSolvLModule (UPol a) (Vector (UPol a)),

   -- from Pol3_:
   VecPol(..), vpRepr, vpEPPOTerm, vpECp, vpToV,
   -- instances for VecPol up to LinSolvLModule (Pol a) (VecPol a),

   -- from RPol_:
   RPol(..), RPol'(..), RPolVarComp, RPolVarsTerm,
   rpolRepr, rpolVComp, rpolVTerm, rvarsTermCp, rvarsTermPref,
   rvarsTermRanges, rpolVPrefix, rpolVRanges, rvarsVolum, 
   showsRVarsTerm, rvarsOfRanges, rp'HeadVar, rpolHeadVar, 
   rp'Vars, rpolVars, cToRPol, varToRPol', varToRPol, rHeadVarPol, 
   rFromHeadVarPol, toRPol, toRPol', fromRPol, substValsInRPol,
   -- instances for RPol', RPol:  Show, Eq, Functor, Dom, PolLike,

   -- from RPol0_
   -- instances for RPol:
   -- Set, AddSemigroup, AddMonoid, AddGroup, MulSemigroup, 
   -- MulMonoid, Num, Fractional, Ring, CommutativeRing, GCDRing,

   vecLDeg, henselLift, testFactorUPol_finField,     -- from Pfact0_

   extendFieldToDeg, det_upol_finField, resultant_1_upol_finField,
                                                     -- from Pfact1_

   module Pfact__,
   -- RseUPol, RseUPolRse, toFromCanFinField, factorUPol_finField,
   -- instance of  FactorizationRing  for  k[x],  k  a finite field

   -- from EPol_:
   EPP, EPPComp, EPPOTerm, EMon, EPol(..),
   eppoECp, eppoMode, eppoWeights, eppoCp,
   epolMons, epolPol, epolEPPOTerm, epolECp, epolPPCp, eLm, eLpp,
   epolLCoord, leastEMon, reordEPol, cToEMon, cToEPol, zeroEPol,
   polToEPol, epolToPol, ecpTOP_weights, ecpPOT_weights, ecpTOP0,
   EPVecP, emonMul, mEPolMul, polEPolMul, epolToVecPol,
   vecPolToEPol, sEPol, mEPVecPMul, sEPVecP,
   -- instances for EPol:
   --             Dom, Cast, PolLike, Show, Eq, Set .. AddGroup, Num

   -- from RdLatP_:
   reduceLattice_UPolField, reduceLattice_UPolField_special,

   -- from FAA0_
   FreeMonoid(..), FreeMOrdTerm,
   freeMN, freeMRepr,  freeMOId, freeMOComp, freeMWeightLexComp,
   -- instances for FreeMonoid:
   --                  Cast FreeMonoid [(Z,Z)],  Show .. MulMonoid,
   --   
   FAA(..), FAAMon, FAAVarDescr,
   faaMons, faaFreeMOrd, faaVarDescr, faaN, faaVMaps, faaFreeMOId,
   faaFreeMOComp, faaLM, faaLeastMon, faaLPP, reordFAA,
   faaMonMul, faaMonFAAMul, cToFAA, faaToHomogForms,
   -- instances for FAA :
   --   Dom, Eq, Show,  Cast (FAA a) (FAAMon a),
   --                   Cast (FAA a) [FAAMon a], Cast (FAA a) a,
   --   PolLike FAA,    Set .. Ring, Fractional,

   faaNF, faaNF_test    -- from FAANF_
  )

where
import Categs  (UMon)
import RsePol_ ()  -- instances for  ResidueE . UPol
import PP_     
import UPol_   hiding (neg_, add_, times_, mul_, shows_)
import UPol0_  
import Pol_    hiding (neg_, add_, times_, mul_, sub_)
import Pol__
import Pol1_
import Pgcd_ ()  -- GCDRing instances for UPol, Pol
import Pol2_   
import Pol3_ (VecPol(..), vpRepr, vpEPPOTerm, vpECp, vpToV)
import RPol_
import RPol0_ ()
import EPol_ 
import Pfact0_ (vecLDeg, henselLift, testFactorUPol_finField)
import Pfact1_ (extendFieldToDeg, det_upol_finField,
                                              resultant_1_upol_finField)
import Pfact__ 
import Pfact3_ ()  -- FactorizationRing instances for  k[x][y], k[x,y]
import RdLatP_
import FAA0_ 
import FAANF_ 
