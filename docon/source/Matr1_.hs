module Matr1_   -- Prelude to the Matrix instances.
                -- All needed from here is  reexported by  VecMatr.

(matrBaseSet, matrBaseAddSemigroup, matrBaseAddGroup, sqMatrBaseSet, 
 sqMatrBaseAddSemigroup, sqMatrBaseMulSemigroup, sqMatrBaseAddGroup, 
 sqMatrBaseRing 
)
where
import qualified Data.Map as Map (empty, lookup, insert)

import DPrelude (PropValue(..), InfUnn(..), lookupProp, showsWithDom)
import Categs 
import SetGroup
import Ring0_
import Matr0_ (MatrixSizes(..), -- class
               SquareMatrix(..), constMt, scalarMt, fromSqMt)




------------------------------------------------------------------------
matrBaseSet  mt@(Mt _ aDom) dom =
  case 
      (Map.lookup Set dom, Map.lookup Set aDom) 
  of
  (Just (D1Set o), _                ) -> (dom, o)
  (_,              Nothing          ) ->
                               (dom,  error ("baseSet (Mt _ dom) _: " ++
                                             " Set not found in  dom\n")
                               )
  (_,              Just (D1Set eSet)) -> 
                                       (Map.insert Set (D1Set o) dom, o)
    where
    o =
     let  
       (h, wd)                   = (mtHeight mt, mtWidth mt)
       (bel, crd, bounds, props) = (membership eSet, osetCard  eSet, 
                                    osetBounds eSet, osetProps eSet
                                   )
       bel' md m =  mtHeight m == h  &&  mtWidth m == wd  && 
                                                        bl md (mtRows m)
                    where  
                    bl 'r' = all (all (bel 'r')) 
                    bl _   = const True
 
       card' = case crd of Fin n -> Fin (n^(h*wd))
                           x     -> x
       (low, up, inf, sup) = bounds
       bounds'             = (low', up', inf', sup')
              where
              [low', up', inf', sup'] = map toMt [low, up, inf, sup]

              toMt (Just (Just x)) = Just $ Just $ constMt mt x
              toMt (Just Nothing ) = Just Nothing 
              toMt _               = Nothing

       props' = [(Finite  , fin),         (IsBaseSet, Yes),
                 (FullType, No ),  -- because the size is fixed

                 (OrderIsTrivial, triv),  (OrderIsTotal, tot),
                 (OrderIsNoether, noet),  (OrderIsArtin, art)
                ]
       [fin, triv, tot, noet, art] = 
                             [lookupProp p props | p <-
                              [Finite, OrderIsTrivial, OrderIsTotal,
                                 OrderIsNoether, OrderIsArtin
                              ]]
     in
     OSet {osetSample  = mt,
           membership  = bel', 
           osetCard    = card', 
           osetPointed = Just $ Just mt, 
           osetList    = Nothing,         -- so far
           osetBounds  = bounds', 
           osetProps   = props',
           osetConstrs = [],
           osetOpers   = []}


------------------------------------------------------------------------
sqMatrBaseSet  mt@(SqMt _ aDom) dom =
  case 
      (Map.lookup Set dom, Map.lookup Set aDom) 
  of
  (Just (D1Set o), _                ) -> (dom, o)
  (_,              Nothing          ) ->
                             (dom, error ("\nbaseSet (SqMt _ dom) _:" ++
                                          "  Set not found in  dom\n")
                             )
  (_,              Just (D1Set eSet)) -> 
                                       (Map.insert Set (D1Set o) dom, o)
    where
    o =
     let n     = mtHeight mt
         setMt = snd $ baseSet (fromSqMt mt) Map.empty    -- not so good
         (belMt, crd, bnds) =
                      (membership setMt, osetCard eSet, osetBounds eSet)

         card' = case crd of Fin k -> Fin (k^(n^2))
                             x     -> x
         (low, up, inf, sup) = bnds 
         bounds'             = (low', up', inf', sup')
                   where
                   [low', up', inf', sup'] = map toM [low, up, inf, sup]

                   toM (Just (Just x)) = Just $ Just $ constMt mt x
                   toM (Just Nothing ) = Just Nothing
                   toM _               = Nothing
     in
     OSet {osetSample  = mt, 
           membership  = (\ md -> belMt md . fromSqMt), 
           osetCard    = card', 
           osetPointed = Just $ Just mt, 
           osetList    = Nothing,        -- so far
           osetBounds  = bounds', 
           osetProps   = osetProps setMt,
           osetConstrs = [],
           osetOpers   = []}


------------------------------------------------------------------------
-- :: AddGroup a => Matrix a -> ...

matrBaseAddSemigroup  mt@(Mt _ aDom) dom =   
  case  
      (Map.lookup AddSemigroup dom, Map.lookup Set aDom)
  of
  (Just (D1Smg s), _                ) -> (dom, s)
  (_,              Nothing          ) ->
                         (dom, error ("\nbaseAddSemigroup (Mt _ dom) _:"
                                      ++ "   Set not found in  dom.\n")
                         )
  (_,              Just (D1Set setA)) ->
      (case 
           Map.lookup AddSemigroup aDom 
       of
       Just (D1Smg sA) -> baseSmg setA sA
       _               ->
                    (dom, error ("\nbaseAddSemigroup (Mt _ dom) _:   "
                                 ++ "AddSemigroup not found in  dom.\n")
                    )
      )
  where 
  baseSmg setA sA = (Map.insert AddSemigroup (D1Smg s) dom, s)
    where
    s = 
      let
        Just (Just zr) = subsmgUnity sA
        zeroMt         = constMt mt zr
        (h,wd)         = (mtHeight mt, mtWidth mt)
        propsA         = subsmgProps sA
        ----------------------------------------------------------------
        gens' = Nothing   -- so far here should 
                          -- be something similar as for Vector
        ----------------------------------------------------------------
        props' = 
          if  (h == 1 && wd == 1) || osetCard setA == Fin 1  then
                                                             propsA
          else
          let [cyc,ord] = [lookupProp p propsA | p <-
                           [IsCyclicSemigroup, IsOrderedSubsemigroup]
                          ]
              cyc'  = if cyc == No then No  
                      else              Unknown   -- so far
          in
          [(Commutative          , Yes ), 
           (IsGroup              , Yes ),  -- recall AddGroup a =>..
           (IsMaxSubsemigroup    , No  ), 
           (IsCyclicSemigroup    , cyc'),  
           (IsOrderedSubsemigroup, ord )]
      in
      Subsemigroup {subsmgType    = Add,
                    subsmgUnity   = Just $ Just zeroMt,
                    subsmgGens    = gens',
                    subsmgProps   = props',
                    subsmgConstrs = [],
                    subsmgOpers   = []}


------------------------------------------------------------------------
sqMatrBaseAddSemigroup  mt@(SqMt _ aDom) dom =  
  case  
      (Map.lookup AddSemigroup dom, Map.lookup Set aDom)
  of
  (Just (D1Smg s), _                ) -> (dom, s)
  (_,              Nothing          ) ->
                      (dom,  error ("\nbaseAddSemigroup (SqMt _ dom) _:"
                                    ++ "   Set not found in  dom.\n")
                      )
  (_,              Just (D1Set setA)) ->
      (case 
           Map.lookup AddSemigroup aDom 
       of
       Just (D1Smg sA) -> baseSmg setA sA
       _               ->
                  (dom, error ("\nbaseAddSemigroup (SqMt _ dom) _:   "
                               ++ "AddSemigroup not found in  dom.\n"))
      )
  where 
  baseSmg setA sA = (Map.insert AddSemigroup (D1Smg s) dom, s)
    where
    s = 
      let
        Just (Just zr) = subsmgUnity sA
        (zeroMt, h)    = (constMt mt zr, mtHeight mt)
        propsA         = subsmgProps sA
        gens'          = Nothing   -- so far here should be 
                                   -- something similar as for Vector
        props' = 
          if  h == 1 || (osetCard setA == Fin 1)  then  propsA
          else
          let [cyc,ord] = [lookupProp p propsA | p <-
                           [IsCyclicSemigroup, IsOrderedSubsemigroup]
                          ]
              cyc'  = if cyc == No then No  
                      else              Unknown   -- so far
          in
          [(Commutative          , Yes ), 
           (IsGroup              , Yes ), -- recall AddGroup a =>..
           (IsMaxSubsemigroup    , No  ), 
           (IsCyclicSemigroup    , cyc'),  
           (IsOrderedSubsemigroup, ord )]
      in
      Subsemigroup {subsmgType    = Add,
                    subsmgUnity   = Just $ Just zeroMt,
                    subsmgGens    = gens',
                    subsmgProps   = props',
                    subsmgConstrs = [],
                    subsmgOpers   = []}


------------------------------------------------------------------------
matrBaseAddGroup  mt@(Mt rows aDom) dom = 
  case  
      (rows, Map.lookup AddGroup dom, Map.lookup AddGroup aDom)  
  of 
  (_,         Just (D1Group g), _                ) -> (dom, g)
  (_,         _,                Nothing          ) ->
                          (dom, error ("\nbaseAddGroup (Mt _ dom) _:" ++
                                       "  AddGroup not found in dom.\n")
                          )           
  ([],        _,                _                ) ->
                            (dom, error "\nbaseAddGroup (Mt [] _) _.\n")
  ([]: _,     _,                _                  ) ->
                        (dom, error "\nbaseAddGroup (Mt ([]:_) _) _.\n")

  ((e: _): _, _,                Just (D1Group gA)) -> 
      (case  
           Map.lookup Set aDom   
       of
       Just (D1Set eS) -> gr e gA eS
       _               -> 
          (dom, error $ showString "\nbaseAddGroup  m@(Mt _ aDom) dom',"
                      $ showsWithDom 1 e "matrHead" "" 
                                         "\nSet not found in aDom.\n"
          )
      )
  where
  gr e gA eS = (Map.insert AddGroup (D1Group g) dom, g)
    where
    g = 
      let
        (zr, h, wd) = (zeroS e, mtHeight mt, mtWidth mt)
        zeroMt      = constMt mt zr
        props_gA    = subgrProps gA
        ------------------------------------------------------------
        gens' = Nothing    -- so far, here should be something 
                           -- similar as for Vector
        ------------------------------------------------------------
        props' = 
         if  (h == 1 && wd == 1) || (osetCard eS == Fin 1)  then 
                                                            props_gA
         else
                    -- Lemma.  If G /= {e}  then  GxG  is not cyclic
         [(IsCyclicGroup,     No ), 
          (IsNormalSubgroup,  Yes), (IsMaxSubgroup, No), 
          (IsPrimeGroup,      No ),
          (IsOrderedSubgroup, lookupProp IsOrderedSubgroup props_gA)]
      in
      Subgroup {subgrType    = Add,
                subgrGens    = gens',
                subgrCanonic = Just $ const zeroMt,
                subgrProps   = props',
                subgrConstrs = [],
                subgrOpers   = []}
          

------------------------------------------------------------------------
sqMatrBaseAddGroup  mt@(SqMt rows aDom) dom = 
  case  
      (rows, Map.lookup AddGroup dom, Map.lookup AddGroup aDom)  
  of 
  (_,         Just (D1Group g), _                ) -> (dom, g)
  (_,         _,                Nothing          ) ->
                        (dom, error ("\nbaseAddGroup (SqMt _ dom) _:" ++
                                     "  AddGroup not found in dom.\n")
                        )           
  ([],        _,                _                ) ->
                          (dom, error "\nbaseAddGroup (SqMt [] _) _.\n")

  ([]: _,     _,                _                ) ->
                      (dom, error "\nbaseAddGroup (SqMt ([]:_) _) _.\n")

  ((e: _): _, _,                Just (D1Group gA)) -> 
      (case  
           Map.lookup Set aDom   
       of
       Just (D1Set eS) -> gr e gA eS
       _               -> 
         (dom,  error $ showString "\nbaseAddGroup m@(SqMt _ dom) dom',"
                      $ showsWithDom 1 e "sqMatrHead m" ""
                                         "\nSet not found in dom.\n")
      )
  where
  gr e gA eS = (Map.insert AddGroup (D1Group g) dom, g)
    where
    g = 
      let (zr, h)  = (zeroS e, mtHeight mt)
          zeroMt   = constMt mt zr
          props_gA = subgrProps gA
          gens'    = Nothing  -- so far
          props'   = 
             if  h == 1 || (osetCard eS == Fin 1)  then  props_gA
             else
             [(IsCyclicGroup,    No ), 
              (IsNormalSubgroup, Yes),  (IsMaxSubgroup, No), 
              (IsPrimeGroup,     No ),
              (IsOrderedSubgroup, lookupProp IsOrderedSubgroup props_gA)]
      in
      Subgroup {subgrType    = Add,
                subgrGens    = gens',
                subgrCanonic = Just $ const zeroMt,
                subgrProps   = props',
                subgrConstrs = [],
                subgrOpers   = []}          


------------------------------------------------------------------------
sqMatrBaseMulSemigroup  mt@(SqMt rows aDom) dom =
  case
      (Map.lookup MulSemigroup dom, Map.lookup MulSemigroup aDom)  
  of 
  (Just (D1Smg s), _              ) -> (dom, s)
  (_,              Nothing        ) ->
                    (dom, error ("\nbaseMulSemigroup (SqMt _ dom) _:  "
                                 ++ "MulSemigroup not found in  dom.\n")
                    )
  (_,              Just (D1Smg rH)) ->
      (case
           (rows, Map.lookup Ring aDom)  
       of 
       ([],        _               ) ->
                      (dom, error "\nbaseMulSemigroup (SqMt [] _) _.\n")

       ([]:_,      _               ) ->
                  (dom, error "\nbaseMulSemigroup (SqMt ([]:_) _) _.\n")

       (_,         Nothing         ) ->
                         (dom, error ("\nbaseMulSemigroup (SqMt _ dom):"
                                      ++ "   Ring not found in  dom.\n")
                         )           
       ((e: _): _, Just (D1Ring rR)) -> baseS e rH rR
      )
  where
  baseS e rH _ = (dom', s)
    where
    dom' = Map.insert MulSemigroup (D1Smg s) dom 
    s    = 
      let
        (n, zr, propsH) = (mtHeight mt, zeroS e, subsmgProps rH)

        unity' = case unity_m e  
                 of
                 Just u -> Just $ Just $ SqMt (scalarMt rows u zr) aDom
                 _      -> Nothing
        props' = 
            if n == 1 then propsH
            else
            let cyc  = lookup IsCyclicSemigroup propsH 
                cycM = if cyc == Just No then No  
                       else                   Unknown  -- so far
            in
            [(Commutative      , No  ), (IsGroup              , No), 
             (IsMaxSubsemigroup, No  ), (IsOrderedSubsemigroup, No),
             (IsCyclicSemigroup, cycM)]
      in
      Subsemigroup {subsmgType    = Mul,
                    subsmgUnity   = unity', 
                    subsmgGens    = Nothing,  --so far
                    subsmgProps   = props',
                    subsmgConstrs = [],
                    subsmgOpers   = []}


------------------------------------------------------------------------
sqMatrBaseRing  mt@(SqMt rows aDom) dom =
  case
      (Map.lookup Ring dom, Map.lookup Ring aDom)  
  of 
  (Just (D1Ring s), _               ) -> (dom, s)
  (_,               Nothing         ) ->
                            (dom,  error ("\nbaseRing (SqMt _ dom) _:  "
                                          ++ "Ring not found in  dom.\n"
                            )            )
  (_,               Just (D1Ring rR)) ->
                (case rows
                 of 
                 []   -> (dom, error "\nbaseRing (SqMt [] _) _.\n")
                 []:_ -> (dom, error "\nbaseRing (SqMt ([]: _) _) _.\n")
                 _    -> baseR rR
                )
  where
  baseR rR = (dom', s)
    where
    dom' = Map.insert Ring (D1Ring s) dom 
    s    = 
      let (n, propsR) = (mtHeight mt, subringProps rR)
          props'      = 
                    if n == 1 then  propsR
                    else
                    [ -- so far, ignore non-commutative rings 
                     (IsField,       No     ), (HasZeroDiv,    Yes    ),
                     (HasNilp,       Yes    ), (IsPrimaryRing, No     ), 
                     (Factorial,     No     ), (PIR,           Unknown), 
                     (IsOrderedRing, No     ), (IsRealField,   No     ),
                     (IsGradedRing,  Unknown)]
      in
      Subring {subringChar    = subringChar rR,
               subringGens    = Nothing,      -- so far
               subringProps   = props',  
               subringConstrs = [],
               subringOpers   = []}
