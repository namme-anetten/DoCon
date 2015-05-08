------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------




module EPol_     -- Extended Polynomial. Continuation. See first  EPol0_
                 -- All needed from here is  reexported by  Pol.
(
 -- instance ...=> LeftModule (Pol a) (EPol a),

 -- module EPol0_:
 EPP, EPPComp, EPPOTerm, EMon, EPol(..),
 eppoECp, eppoMode, eppoWeights, eppoCp, epolMons, epolPol, 
 epolEPPOTerm, epolECp, epolPPCp, eLm, eLpp, epolLCoord, leastEMon, 
 reordEPol, cToEMon, cToEPol, zeroEPol, polToEPol, epolToPol, 
 ecpTOP_weights, ecpPOT_weights, ecpTOP0,
 -- , instances
 -- Dom, Cast, PolLike, Show, DShow, Eq, Set .. AddGroup, Num

 -- module EPol1_:
 EPVecP, emonMul, mEPolMul, polEPolMul, epolToVecPol, 
 vecPolToEPol, sEPol, mEPVecPMul, sEPVecP
)
where
import qualified Data.Map as Map (lookup, insert)

import DPrelude (InfUnn(..), PropValue(..), lookupProp, showsWithDom)
import Categs (Dom(..), CategoryName(..), Domain1(..), Domain2(..), 
               Subring(..), Submodule(..), Property_Subring(..),
               Property_Submodule(..), Property_SubmoduleGens(..)
              )
import RingModule (CommutativeRing(), LeftModule(..))
import Pol_       (Pol(..))
import EPol0_      
import EPol1_      




------------------------------------------------------------------------
instance CommutativeRing a => LeftModule (Pol a) (EPol a)
  where
  cMul = polEPolMul

  baseLeftModule (pol, _) fdom = 
    case
        (Map.lookup LeftModule fdom, dom pol)
    of
    (Just (D2Module t), _ ) -> (fdom, t)
    (_,                 aD) -> 
        (case Map.lookup Ring aD
         of
         Nothing          -> (fdom, error msg)
         Just (D1Ring aR) -> bm $ subringProps aR
        )
        where
        msg = concat ["\nbaseLeftModule (samplePol,sampleEPol) \
                      \currentDom,", showsWithDom 1 pol "samplePol" 
                      "R[..]" "\nRing term not found in  R.\n"]
        bm propsA =
          let
            genProps = [(IsFreeModuleBasis, No ), (IsGxBasisM, No)]
            props    = [(IsFreeModule,      Yes),
                        (IsPrimeSubmodule,  No ),
                                            -- for it is the full module
                        (IsPrimarySubmodule, No),    --
                        (IsMaxSubmodule,     No),    --
                        (HasZeroDivModule,   hasZD),
                        (IsGradedModule,     No   )  -- so far
                       ]
            hasZD = lookupProp HasZeroDiv propsA
            t     = 
              Submodule
               {moduleRank    = Infinity, moduleGens     = Nothing,
                moduleProps   = props,    moduleGenProps = genProps,
                moduleConstrs = [],       moduleOpers    = []}
          in
          (Map.insert LeftModule (D2Module t) fdom, t)
