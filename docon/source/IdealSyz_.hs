------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge D.Mechveliani,  2012
------------------------------------------------------------------------
------------------------------------------------------------------------




module IdealSyz_     -- Tools for setting  Ideals and Subrings.
                     -- All needed from here is  reexported by  Residue.
(gensToIdeal)
where
import qualified Data.Map as Map (lookup, insert) 

import Data.Maybe (fromJust)

import DPrelude (Length(..), -- class 
                 InfUnn(..), PropValue(..), lookupProp, updateProps)
import Categs     
import SetGroup (Set(..), AddSemigroup(..), MulSemigroup(..), 
                 AddGroup(..), zeroS, unity
                )
import RingModule (Ring(..), LinSolvRing(..),zeroIdeal, unityIdeal)





------------------------------------------------------------------------
gensToIdeal :: LinSolvRing a => [a]                 ->         -- igens
                                [Factorization a]   ->         -- fts
                                Properties_IdealGen ->         -- bProps
                                Properties_Ideal    ->         -- iProps
                                Domains1 a          ->         -- dR
                                Domains1 a          ->         -- dm
                                (Domains1 a, Ideal a)

  -- Make an ideal  I  from the generator list  igens  in a  base
  -- ring  R  possessing the property  (ModuloBasisDetaching,Yes).
  --
  -- dR      is a base domain filled up to LinSolvRingTerm,
  -- dm      is the current domain (usually empty) to be loaded 
  --           further with the ideal and its accompanying domain 
  --           descriptions
  -- iProps  is the sublist of the full property list.
  --
  -- fts   is ignored if it is given empty Or  Factorial/=Yes in R
  --                                       Or  Prime==Yes  for I,
  --       otherwise
  --       fts   contains the given factorizations for each basis 
  --       element (see `factor'), each unknown factorization is
  --       denoted by  [],
  --       in this case `igens' remains as it is given.
  --
  -- ATTENTION:
  -- If it is known that `igens' is a  gx-basis (see Manual), then 
  -- better set this explicitly in  bProps  (IsGxBasis,Yes). 
  -- Otherwise it will still compute  gxBasis  and set it in ideal 
  -- instead of the initial one.
  --
  -- For the most important ideal properties, such as Prime,
  -- Primary, IsMaxIdeal, it is better to set them explicitly in 
  -- iProps  (if the value is known). 
  -- gensToIdeal   tries to make the properties more definite -  
  -- using also  fts, R properties.  In particular, it completes 
  -- the values according to the dependencies between Prime,
  -- Primary, IsMaxIdeal.
  -- But it does *not* apply the primality test.
  ----------------------------------------------------------------

gensToIdeal igens fts bProps iProps dR dm = 
  let
    Just (D1Set setR) = Map.lookup Set dR  

    e           = fromJust $ fromJust $ osetPointed setR
    (zr, un)    = (zeroS e, unity e)
    (dR1, rR)   = baseRing zr dR
    (dR2, syzR) = baseLinSolvRing zr dR1
    gMode       = case lookup IsGxBasis bProps of Just Yes -> "g"
                                                  _        -> ""
    propsR    = subringProps rR
    syzRProps = linSolvRingProps syzR
    detaching = lookupProp ModuloBasisDetaching syzRProps

    [maxI, primeI, primaryI] = [lookupProp p iProps | 
                                       p <- [IsMaxIdeal, Prime, Primary]
                               ]
    [fact, pir] = [lookupProp p propsR | p <- [Factorial, PIR]]

    igens' = if gMode == "g" then   igens  else  fst $ gxBasis igens

    reducedUn = fst $ moduloBasis gMode igens' un

                    -- reducedUn == zr  <=>  I = R,   
                    -- igens'    == []  <=>  I = {0},
                    --
                    -- and the below settings in  `let .. in'  are
                    -- only for the case of non-unity and non-zero I
    --------------------------------------------------------------------
    constructions' =  
               if  primeI == Yes || fact /= Yes || gMode == ""  then  []
               else                              [GenFactorizations fts]

    nonprimaryItem fs =  genLength fs > 1
    nonprimeItem   fs =  nonprimaryItem fs || np fs 
                                                 where     
                                                 np ((_, k): _) = k > 1
    prime' = case (maxI, primeI, any nonprimeItem fts)  
             of
             (Yes, _,   _   ) -> Yes
             (_,   Yes, _   ) -> Yes
             (_,   No,  _   ) -> No
             (_,   _,   True) -> No
             _                -> case fts of [[(_, 1)]] -> Yes
                                             _          -> Unknown
    max' = case (maxI, prime', pir) 
           of
           (No,  _,   _  ) -> No
           (Yes, No,  _  ) -> 
                    error $ msg "(IsMaxIdeal, Yes)  from iProps \
                                \contradicts the deduced (Prime, No).\n"
           (_,   No,  _  ) -> No
           (Yes, _,   _  ) -> Yes
           (_,   Yes, Yes) -> Yes
           _               -> Unknown

    msg = 
        showString "\ngensToIdeal generators fts bProps iProps dR dm,\n\ 
                   \dR         = " . showsDomOf 1 e .
        showString "\nbProps     = " . shows bProps .
        showString "\niProps     = " . shows iProps .
        showString "\ngenerators = " . shows igens  . showString "\n:\n"

    primary' = case (prime', primaryI, any nonprimaryItem fts)
               of
               (Yes, _  , _   ) -> Yes
               (_,   Yes, _   ) -> Yes
               (_,   No , _   ) -> No
               (_,   _,   True) -> No
               _                -> case fts of [[_]] -> Yes
                                               _     -> Unknown
    iProps' = [(IsMaxIdeal, max'), (Prime, prime'), (Primary, primary')]
    bProps' = [(IsGxBasis, Yes)]
    --------------------------------------------------------------------
    (dm1, setI)     = idealGensToSubset' zr rR propsR [] igens' dR2 dm  
    (dm2, aSemigrI) = idealSetToAddSubsemigroup' zr [] dR2 dm1  
    (dm3, aGrI)     = idealGensToAddSubgroup' zr [] igens' dR2 dm2 
    (dm4, mSemigrI) = ringAddSubgroupToMulSubsemigroup'
                                        zr setI aSemigrI aGrI [] dR2 dm3
    (dm5, _) = idealGrSemigrToSubring' propsR aGrI mSemigrI [] dR2 dm4
    --------------------------------------------------------------------
    iI = case (igens', reducedUn == zr) 
         of
         ([], _   ) -> zeroIdeal iProps rR   
         (_,  True) -> unityIdeal un rR 
         _          -> Ideal {idealGens     = Just igens',
                              idealProps    = iProps',
                              idealGenProps = bProps',
                              idealConstrs  = constructions',
                              idealOpers    = []}
    --------------------------------------------------------------------
  in
  case detaching
  of
  Yes -> (Map.insert IdealKey (D1Ideal iI) dm5, iI)
  _   -> 
        error $ msg "R  needs to possess (ModuloBasisDetaching, Yes).\n"




-- Auxiliary local things:

------------------------------------------------------------------------
idealGensToSubset' :: LinSolvRing a =>
                      a                  ->
                      Subring a          ->
                      Properties_Subring -> 
                      Properties_OSet    ->
                      [a]                ->
                      Domains1 a         -> 
                      Domains1 a         -> (Domains1 a, OSet a)

-- gens  is a  non-empty gx-basis of I,  I is not unity.

idealGensToSubset' zr  _rR  propsR givenProps gens dR dm = 
                                        (Map.insert Set (D1Set o) dm, o)
  where
  o =
   let
     (_, setR)        = baseSet zr dR
     (bel, propsSetR) = (membership setR, osetProps setR)

     bel' md x = (fst (moduloBasis "g" gens x)) == zr  &&  bl md x
                                                   where
                                                   bl 'r' = bel 'r'
                                                   bl _   = const True
     hasZD = lookupProp HasZeroDiv propsR
     cardR = osetCard setR
     card' = case (hasZD, cardR) of (No, Infinity) -> Infinity 
                                    _              -> UnknownV -- so far
     -------------------------------------------------------------------
     [fin, ordTriv, ordTot, ordNoet, ordArt] =  
                                 [lookupProp p propsSetR | p <-
                                  [Finite, OrderIsTrivial, OrderIsTotal,
                                   OrderIsNoether, OrderIsArtin
                                 ]]
     props' = [(FullType,       No      ), (IsBaseSet, No), 
               (Finite,         fin'    ),
               (OrderIsTrivial, ordTriv'), 
               (OrderIsTotal,   tot'    ), (OrderIsNoether, noet'),
               (OrderIsArtin,   art'    )
             ]
     props''  = updateProps givenProps props'
     ordTriv' = if ordTriv == Yes then Yes  else Unknown
     fin' = case (hasZD, fin) of (_,  Yes) -> Yes
                                 (No, No ) -> No
                                 _         -> Unknown  -- so far
     tot' = case (ordTot, ordTriv) of (Yes, _  ) -> Yes
                                      (_,   Yes) -> No
                                      _          -> Unknown  -- so far

     noet' = case (ordNoet,ordTriv, fin') of 
                                     (Yes, _,   _  )-> Yes
                                     (_,   Yes, _  )-> Yes
                                     (_,   _,   Yes)-> Yes
                                     _              -> Unknown -- so far
     art' = case (ordArt, ordTriv, fin') of 
                                     (Yes, _  , _  )-> Yes
                                     (_,   Yes, _  )-> Yes
                                     (_,   _,   Yes)-> Yes
                                     _              -> Unknown -- so far
     list' = Nothing   -- so far 
                       -- In some cases, we might list the ideal
     ------------------------------------------------------------------- 
   in
   OSet
   {osetSample = zr,       membership  = bel',
    osetCard   = card',    osetPointed = Just $ Just zr,
    osetList   = list',    osetBounds  = osetBounds setR,  -- so far
    osetProps  = props'',  osetConstrs = [],
    osetOpers  = []}


------------------------------------------------------------------------
-- This is specially for calling from  gensToIdeal.
-- I is non-trivial.

idealSetToAddSubsemigroup' zr givenProps dR dm = 
                               (Map.insert AddSemigroup (D1Smg s) dm, s)
  where
  s =
   let
     (_, semigA) = baseAddSemigroup zr dR
     propsA      = subsmgProps semigA
     smgGens     = Nothing   -- so far 
     -------------------------------------------------------------------
     cyc     = lookupProp IsCyclicSemigroup     propsA
     ordered = lookupProp IsOrderedSubsemigroup propsA
     props' = [(Commutative,           Yes ), (IsGroup,           Yes ),
               (IsCyclicSemigroup,     cyc'), (IsMaxSubsemigroup, max'),
               (IsOrderedSubsemigroup, ord')
              ]
     props'' = updateProps givenProps props'
     ord' = case ordered of Yes -> Yes
                            _   -> Unknown   -- so far
     cyc' = case cyc of Yes -> Yes
                        _   -> Unknown   -- so far
     max' = Unknown   -- so far
   in
   Subsemigroup {subsmgType    = Add,      subsmgUnity = Just $ Just zr,
                 subsmgGens    = smgGens,  subsmgProps = props'',
                 subsmgConstrs = [],       subsmgOpers = []}


------------------------------------------------------------------------
-- This is specially for the calling from  gensToIdeal.
-- Ideal is non-trivial,  gens  is a gx-basis,
-- setH, smgH, syzRProps  are built earlier.

idealGensToAddSubgroup' zr givenProps gens dR dm =
  let
    (dR1, gA)  = baseAddGroup zr dR
    (_, syzR) = baseLinSolvRing zr dR1
    syzRProps = linSolvRingProps syzR
    props_gA  = subgrProps gA
    canonic   = lookup ModuloBasisCanonic syzRProps 

    Just (D1Set setH) = Map.lookup Set dm
    props_setH        = osetProps setH
                           
    can' = case canonic     -- canonical projection modulo subgroup
           of  
           Just Yes -> Just (fst . moduloBasis ("cg") gens)
           _        -> Nothing
            
    grGens = Nothing  -- so far. 
                      -- In some cases, we might find the generators
    --------------------------------------------------------------------
    cyc     = lookupProp IsCyclicGroup     props_gA
    ordered = lookupProp IsOrderedSubgroup props_gA
    props'  = [(IsNormalSubgroup,  Yes ), (IsPrimeGroup , prime'),
               (IsCyclicGroup,     cyc'), (IsMaxSubgroup, max'  ),
               (IsOrderedSubgroup, ord')
              ]
    props'' = updateProps givenProps props'
    ord' = case ordered of Yes -> Yes
                           _   -> Unknown   -- so far

    prime' = case lookup Finite props_setH  of  Just No -> No
                                                _       -> Unknown
                                                           -- so far
    cyc' = case (cyc, prime') of (Yes, _  ) -> Yes
                                 (_,   Yes) -> Yes
                                 _          -> Unknown  -- so far
    max' = Unknown   -- so far
    --------------------------------------------------------------------
    g = Subgroup {subgrType    = Add,   subgrGens  = grGens, 
                  subgrCanonic = can',  subgrProps = props'',
                  subgrConstrs = [],    subgrOpers = []}
  in
  (Map.insert AddGroup (D1Group g) dm, g)


------------------------------------------------------------------------
-- This is specially for calling from  gensToIdeal.
-- Ideal is non-trivial,  setH,smg_aH,agH  are built earlier.

ringAddSubgroupToMulSubsemigroup' zr setH  _       _  givenProps dR dm =
                                      -- smg_aH agH
  let
    cardin       = osetCard  setH
    (_, smg_mR)  = baseMulSemigroup zr dR      
    props_smg_mR = subsmgProps smg_mR
    gens'        = Nothing  -- so far
    --------------------------------------------------------------------
    [comm, ordr] = [lookupProp p props_smg_mR | 
                              p <- [Commutative, IsOrderedSubsemigroup]]
    props' = [(IsGroup,               No   ),
              (Commutative,           comm'), 
              (IsCyclicSemigroup,     cyc' ), 
              (IsMaxSubsemigroup,     max' ),
              (IsOrderedSubsemigroup, ord' )
             ]
    props'' = updateProps givenProps props'
    comm' = case (comm, cardin) of (Yes, _    ) -> Yes
                                   (_  , Fin 2) -> Yes
                                   _            -> Unknown -- so far
    ord' = case ordr of Yes -> Yes
                        _   -> Unknown   
    cyc' = Unknown  -- so far
    max' = Unknown  -- so far
    s = Subsemigroup {subsmgType    = Mul,   subsmgUnity = Just Nothing,
                      subsmgGens    = gens', subsmgProps = props'',
                      subsmgConstrs = [],    subsmgOpers = []}
  in
  (Map.insert MulSemigroup (D1Smg s) dm, s)


------------------------------------------------------------------------
-- This is specially for calling from  gensToIdeal.
-- Ideal is non-trivial,  aG',mSmg'  are built earlier.


idealGrSemigrToSubring' propsR  _   _     givenProps _  dm = 
                             -- aG' mSmg'            dR  
  let
    gens' = Nothing   -- so far 
    --------------------------------------------------------------------
    [ordered, hasZD, primary] = 
                        [lookupProp p propsR |
                         p <- [IsOrderedRing, HasZeroDiv, IsPrimaryRing]  
                        ]
    props' =                               -- here R' does not contain 1
             [(IsField,        No      ), 
               (Factorial,     No      ), (HasZeroDiv,    hasZD'  ), 
               (HasNilp,       hasNilp'), (IsPrimaryRing, primary'),  
               (PIR,           pir'    ), (IsRealField,   No      ), 
               (IsOrderedRing, ord'    ), (IsGradedRing,  No      )
              ]
    props''  = updateProps givenProps props'
    ord'     = case ordered of Yes -> Yes
                               _   -> Unknown   -- so far
    hasZD'   = case hasZD   of No  -> No
                               _   -> Unknown   -- so far 
    hasNilp' = case hasZD   of No  -> No
                               _   -> Unknown   -- so far 
    primary' = case primary of Yes -> Yes
                               _   -> Unknown   -- so far 
    pir'  = Unknown    -- so far
    char' = Nothing    -- for this subring has not unity
    --------------------------------------------------------------------
    r = Subring {subringChar    = char',    subringGens    = gens',
                 subringProps   = props'',  subringConstrs = [],
                 subringOpers   = []}
  in
  (Map.insert Ring (D1Ring r) dm, r)




{- do we need this? *************************************
-- subset of a non-unity ideal  I  given by the generators in a  
-- (base) ring  R  possessing the property 
-- (ModuloBasisDetaching,Yes)
idealGensToSubset ::   LinSolvRing a =>
   String -> Properties_OSet -> [a] -> Domains1 a -> Domains1 a ->
                                                 (Domains1 a,OSet a)
idealGensToSubset mode givenProps gens dR dm =
  -- mode = "" | "g",   the latter means IsGxBasis==Yes.
  -- givenProps   (may be []) contains some property values
  --              for the result; the function updates them.
  -- dR  is a base domain filled up to LinSolvRingTerm,
  -- dm  is the current domain - to be filled further.
  let   Just (D1Set setR) = Map.lookup dR Set 
    e        = fromJust $ fromJust $ osetPointed setR
    zr       = zeroS e;  (dR1,rR) = baseRing zr dR
    propsR   = subringProps rR
    gens'    = filter (/= zr) gens
                       -- inside this `let..in' 
                       -- I is non-zero, that is  not (null gens')
    propsSetR  = osetProps setR;  (dR2,syzT) = baseLinSolvRing zr dR1 
    syzProps   = syzRingProps syzT
    detaching  = lookupProp ModuloBasisDetaching syzProps
    bel' x = (fst $ moduloBasis mode gens' x)==zr
    hasZD = lookupProp HasZeroDiv propsR;  cardR = osetCard setR
    card' = case (hasZD,cardR)  of (No, Infinity) -> Infinity
            _              -> UnknownV    -- to be developed
    ----------------------------------------------------------------
    [fin,ordTriv,ordTot,ordNoet,ordArt] =  
                               [lookupProp p propsSetR | p <-
                                [Finite,OrderIsTrivial,OrderIsTotal,
                                 OrderIsNoether,OrderIsArtin  ]]
    props' = [(FullType      , No  ), (IsBaseSet, No), 
              (Finite        , fin'), (OrderIsTrivial,ordTriv'), 
              (OrderIsTotal  , tot'), (OrderIsNoether, noet'),
              (OrderIsArtin  , art')    ]
    props''  = updateProps givenProps props' 
    ordTriv' = if  ordTriv==Yes  then Yes  else Unknown
    fin' = case  (hasZD,fin)  of  (_ , Yes) -> Yes;  (No, No ) -> No
                                  _         -> Unknown -- so far
                     -- Here should be something similar to  card'
    tot'  = case  (ordTot,ordTriv)  of  (Yes, _  ) -> Yes
                                   (_  , Yes) -> No
                                   _          -> Unknown  --so far
    noet' = case  (ordNoet,ordTriv,fin')  of 
                    (Yes, _  , _  )-> Yes    (_  , Yes, _  )-> Yes
                                (_  , _  , Yes)-> Yes
                                _              -> Unknown --so far
    art'  = case  (ordArt,ordTriv,fin')  of (Yes, _  , _  )-> Yes
                           (_  , Yes, _  )-> Yes  (_  , _  , Yes)-> Yes
                                _              -> Unknown --so far
    list' = Nothing      -- so far 
                         -- In some cases, we might list the ideal
    os = OSet {osetSample  = zr,          membership  = bel', 
               osetCard    = card',  osetPonited = Just (Just zr), 
               osetList    = list',
               osetBounds  = osetBounds setR, -- so far
               osetProps   = props'',    osetConstrs = [], 
               osetOpers   = []}
    set0 = listToSubset [zr] [] setR
    --------------------------------------------------------------
  in  case  (gens', detaching)
  of ([], _  ) -> (Map.insert Set (D1Set set0) dm , set0)  
    (_ , Yes) -> (Map.insert Set (D1Set os) dm, os  )    
    _         -> error ("idealGensToSubset:  \nbase ring "++
                        "needs (ModuloBasisDetaching,Yes)\n"
                       )
*******************************************************************
-}
