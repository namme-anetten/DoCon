module Vec1_   -- Prelude to Vector instances.
               -- All needed from here is  reexported by   VecMatr.

  (vecBaseSet, vecBaseAddSemigroup, vecBaseAddGroup, 
   vecBaseMulSemigroup, vecBaseMulGroup, vecBaseRing
  )
where
import qualified Data.Map as Map (empty, lookup, insert)
 
import Categs 
import DPrelude (Length(..), -- class 
                 PropValue(..), InfUnn(..), 
                 lookupProp, listsOverList, fmapfmap)
import SetGroup
import Ring0_  
import Vec0_ (vecSize, constVec)





------------------------------------------------------------------------
vecBaseSet :: Set a => Vector a -> Domains1 (Vector a) ->
                                  (Domains1 (Vector a), OSet (Vector a))
vecBaseSet v dm =  
  (case  
       (vecRepr v, Map.lookup Set dm)  
   of
     (_,    Just (D1Set o)) -> (dm, o)
     (a: _, _             ) -> vset $ snd $ baseSet a Map.empty
     _                      -> (dm, error "baseSet (Vec []) dom'\n")
  )
  where
  vset s = (Map.insert Set (D1Set o) dm, o)
    where
    o =
      let   -- mind that the components of  v  are presumed to 
            -- belong to baseSet ...

        (bel, crd, list, bounds, props) = 
                              (membership s, osetCard s, osetList s,
                               osetBounds s, osetProps s
                              )
        size  = vecSize v
        card' = case crd of Fin n    -> Fin (n^size)
                            Infinity -> Infinity
                            _        -> UnknownV

        bel' md (Vec xs) = (genLength xs) == size && bl md xs
                                             where
                                             bl 'r' = all (bel 'r')
                                             bl _   = const True
        list' = case list 
                of 
                Just xs -> Just $ map Vec $ listsOverList size xs
                _       -> Nothing 

        bounds' = (low', up', inf', sup') 
                  where
                  [low', up', inf', sup'] = map toV [low, up, inf, sup]
                  (low, up, inf, sup)     = bounds
                  toV                     = fmapfmap (constVec v)

        props' = [(Finite, fin),   (IsBaseSet, Yes),
                  (FullType, No),  -- because the size is fixed

                  (OrderIsTrivial, triv), (OrderIsTotal, tot),
                  (OrderIsNoether, noet), (OrderIsArtin, art)
                 ]
        [fin, triv, tot, noet, art] = 
                               [lookupProp p props | p <-
                                [Finite, OrderIsTrivial, OrderIsTotal,
                                 OrderIsNoether,OrderIsArtin
                               ]]
      in
      OSet {osetSample = v,        membership  = bel',
            osetCard   = card',    osetPointed = Just $ Just v, 
            osetList   = list',    osetBounds  = bounds', 
            osetProps  = props',   osetConstrs = [],
            osetOpers  = []}


------------------------------------------------------------------------
--  :: AddGroup a => Vector a -> ...

vecBaseAddSemigroup v dm =  
  (case  
       (Map.lookup AddSemigroup dm, vecRepr v)
   of
   (Just (D1Smg s), _   ) -> (dm, s)
   (_,              a: _) -> vsmg (zeroS a) $ upAddSemigroup a Map.empty
   _                      -> 
                          (dm, error "baseAddSemigroup (Vec []) vDom\n")
  )
  where
  vsmg zr domA = 
    case (Map.lookup Set domA, Map.lookup AddSemigroup domA)  
    of
    (Just (D1Set setA), Just (D1Smg sA)) -> 
                               (Map.insert AddSemigroup (D1Smg s) dm, s)
      where
      s = 
       let
         zeroV@(Vec zrs) = constVec v zr
         (gensA, propsA) = (subsmgGens sA, subsmgProps sA)
         ---------------------------------------------------------------
         gens' = 
           case gensA 
           of
           Nothing -> Nothing
           Just gs -> Just $ map Vec $ vgens zrs gs
               where                      -- optimizations possible 
               vgens []      _  = []
               vgens (_: xs) gs =
                       [(y: xs) | y <- gs] ++ (map (zr :) $ vgens xs gs)
         ---------------------------------------------------------------
         props' = 
           if (vecSize v == 1) || (osetCard setA == Fin 1) then  propsA
           else
           let cyc = lookupProp IsCyclicSemigroup     propsA
               ord = lookupProp IsOrderedSubsemigroup propsA
               cyc'= if cyc == No then No  
                     else              Unknown   -- SO FAR
           in
           [(Commutative,           Yes ), 
            (IsGroup,               Yes ),  -- recall AddGroup a =>...
            (IsMaxSubsemigroup,     No  ), 
            (IsCyclicSemigroup,     cyc'),  
            (IsOrderedSubsemigroup, ord )]
       in
       Subsemigroup 
       {subsmgType    = Add,    subsmgUnity = Just $ Just zeroV,
        subsmgGens    = gens',  subsmgProps = props',
        subsmgConstrs = [],     subsmgOpers = [] }


------------------------------------------------------------------------
vecBaseAddGroup v dm = 
  (case  
       (vecRepr v, Map.lookup AddGroup dm)
   of 
   (_,    Just (D1Group g)) -> (dm, g)
   (a: _, _               ) -> vgr (zeroS a) $ upAddGroup a Map.empty
   _                        ->
                              (dm, error "baseAddGroup (Vec []) vDom\n")
  )
  where
  vgr zr aDom = 
    case (Map.lookup Set aDom, Map.lookup AddGroup aDom) 
    of
    (Just (D1Set aS), Just (D1Group aG)) -> 
                                 (Map.insert AddGroup (D1Group g) dm, g)
      where
      g = 
       let
         zeroV@(Vec zrs)     = constVec v zr
         (gens_aG, props_aG) = (subgrGens aG, subgrProps aG)
         ---------------------------------------------------------------
         gens' = 
           case gens_aG 
           of
           Nothing -> Nothing
           Just gs -> Just $ map Vec $ vgens zrs gs
                where                     -- optimizations are possible
                vgens []      _  = []
                vgens (_: xs) gs = 
                       [(y: xs) | y <- gs] ++ (map (zr :) $ vgens xs gs)
         ---------------------------------------------------------------
         props' = 
          if (vecSize v == 1) || (osetCard aS == Fin 1) then  props_aG
          else
                        -- Lemma.  If G /= {e}  then  GxG  is not cyclic
          [(IsCyclicGroup,     No ), 
           (IsNormalSubgroup,  Yes), (IsMaxSubgroup, No), 
           (IsPrimeGroup,      No ),
           (IsOrderedSubgroup, lookupProp IsOrderedSubgroup props_aG)]
       in
       Subgroup {subgrType    = Add,   
                 subgrGens    = gens', 
                 subgrCanonic = Just $ const zeroV,
                                      -- A is full, hence A+...+A is too
                 subgrProps   = props',
                 subgrConstrs = [],          
                 subgrOpers   = []}


------------------------------------------------------------------------
vecBaseMulSemigroup v dm =  
  (case 
       (vecRepr v, Map.lookup MulSemigroup dm)
   of
   (_,     Just (D1Smg s)) -> (dm, s)
   (e: xs, _             ) ->
                 mulsmg (e: xs) (unity_m e) $ upMulSemigroup e Map.empty
   _                      ->
                          (dm, error "baseMulSemigroup (Vec []) vDom\n")
  )
  where  
  mulsmg xs un_m eDom = 
    case 
        (Map.lookup Set eDom, Map.lookup MulSemigroup eDom)  
    of
    (Just (D1Set eSet), Just (D1Smg eH)) -> 
                               (Map.insert MulSemigroup (D1Smg s) dm, s)
     where
     s = 
      let
        size              = vecSize v
        (eHgens, eHprops) = (subsmgGens eH, subsmgProps eH)

        unV'_m = case un_m of Just u -> Just $ Just $ constVec v u
                              _      -> Nothing
        ----------------------------------------------------------------
        gens' = 
          case eHgens 
          of                   -- optimizations possible 
          Nothing -> Nothing
          Just gs -> case un_m  
                     of
                     Nothing -> Just $ map Vec $ listsOverList size gs
                     Just u  -> Just $ map Vec $ vgens uns
                          where
                          uns           = map (const u) xs
                          vgens []      = []
                          vgens (_: xs) =
                             [y: xs | y <- gs] ++ (map (u :) $ vgens xs)
        ----------------------------------------------------------------
        props' = 
          if size == 1 || (osetCard eSet == Fin 1) then  eHprops
          else
          let [comm, group, cyc, ord] = 
                              [lookupProp p eHprops | p <-
                               [Commutative, IsGroup, IsCyclicSemigroup,
                                IsOrderedSubsemigroup
                              ]]
              cyc' = if cyc == No then No  
                     else              Unknown   -- SO FAR
          in
          [(IsMaxSubsemigroup,     No   ), (Commutative,       comm), 
           (IsGroup,               group), (IsCyclicSemigroup, cyc'), 
           (IsOrderedSubsemigroup, ord  )]
      in
      Subsemigroup {subsmgType    = Mul,    subsmgUnity = unV'_m, 
                    subsmgGens    = gens',  subsmgProps = props',
                    subsmgConstrs = [],     subsmgOpers = []}



------------------------------------------------------------------------
vecBaseMulGroup v dm = 
  (case  
       (vecRepr v, Map.lookup MulGroup dm)
   of 
   (_,    Just (D1Group g)) -> (dm, g)
   (e: _, _               ) -> gr (unity e) $ upMulGroup e Map.empty
   _                        ->
                              (dm, error "baseMulGroup (Vec []) vDom\n")
  )
  where
  gr un eDom =  
    case (Map.lookup Set eDom, Map.lookup MulGroup eDom) 
    of
    (Just (D1Set eS), Just (D1Group eG)) ->
                                 (Map.insert MulGroup (D1Group g) dm, g)
     where
     g = 
      let
        unVec@(Vec uns)    = constVec v un
        (gens_eG,props_eG) = (subgrGens eG, subgrProps eG)
        ----------------------------------------------------------------
        gens' = 
          case gens_eG 
          of
          Nothing -> Nothing
          Just gs -> Just $ map Vec $ vgens uns gs
            where                          -- optimizations possible 
            vgens []      _  = []
            vgens (_: xs) gs = 
                       [(y: xs) | y <- gs] ++ (map (un :) $ vgens xs gs)
        ----------------------------------------------------------------
        props' = 
          if (vecSize v == 1) || (osetCard eS == Fin 1) then  props_eG
          else
          [(IsCyclicGroup,     No ), (IsMaxSubgroup, No), 
           (IsPrimeGroup,      No ),
           (IsNormalSubgroup,  Yes),   -- for it is full
           (IsOrderedSubgroup, lookupProp IsOrderedSubgroup props_eG)]
      in
      Subgroup 
      {subgrType    = Mul,                 subgrGens  = gens', 
       subgrCanonic = Just $ const unVec,  subgrProps = props',
       subgrConstrs = [],                  subgrOpers = []}


------------------------------------------------------------------------
vecBaseRing v dm = 
  (case  
       (vecRepr v, Map.lookup Ring dm)
   of 
   (_,     Just (D1Ring r)) -> (dm, r)
   (e: xs, _              ) -> 
                    rg (e:xs) (zeroS e) (unity_m e) $ upRing e Map.empty

   _                       -> (dm, error "baseRing (Vec []) vDom\n")
  )
  where
  rg xs zr un_m eDom = 
    case (Map.lookup Set eDom, Map.lookup Ring eDom) 
    of
    (Just (D1Set eS), Just (D1Ring eR)) -> 
                                      (Map.insert Ring (D1Ring r) dm, r)
     where
     r = 
       let
         zrs             = map (const zr) xs
         (eGens, eProps) = (subringGens eR, subringProps eR)
         ---------------------------------------------------------------
         gens' = 
           case eGens 
           of
           Nothing -> Nothing
           Just gs -> Just $ map Vec $ vgens zrs gs
                where                          -- optimizations possible 
                vgens []      _  = []
                vgens (_: xs) gs =
                       [(y: xs) | y <- gs] ++ (map (zr :) $ vgens xs gs)
         ---------------------------------------------------------------
         props' = 
           if (vecSize v == 1) || (osetCard eS == Fin 1) then  eProps
           else
           let names = [HasNilp, PIR, IsOrderedRing, IsPrimaryRing]
               [hasNilp, pir, ord, primary] =
                                      [lookupProp p eProps | p <- names]

               primary' = case (un_m, primary) of  
                                                 (Just _, _ ) -> No
                                                 (_,      No) -> No
                                                 _            -> Unknown
           in
           [(IsField,       No      ), (HasZeroDiv,    Yes    ), 
            (Factorial,     No      ), (HasNilp,       hasNilp), 
            (IsPrimaryRing, primary'), (IsRealField,   No     ),   
            (PIR,           pir     ), (IsOrderedRing, ord    ),
            (IsGradedRing,  Unknown )]
       in
       Subring {subringChar  = char zr,  subringGens    = gens',
                subringProps = props',   subringConstrs = [],
                subringOpers = []}