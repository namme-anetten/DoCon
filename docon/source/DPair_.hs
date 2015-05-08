module DPair_          -- Prelude for  DPair.  
                       -- All needed from here is  reexported by  DPair.

(directProduct_set, directProduct_semigroup,
 directProduct_group, directProduct_ring
)
where
import Data.Maybe (fromMaybe) 

import DPrelude (PropValue(..), InfUnn(..), and3, or3, allMaybes,
                                        boolToPropV, lookupProp, showsn)
import SetGroup (Set(..), isoGroup)
import Ring0_   (Ring(..))
import Categs 





------------------------------------------------------------------------
directProduct_set :: (Set a, Set b) => OSet a -> OSet b -> OSet (a, b)
directProduct_set                      xX        yY =  

  OSet {osetSample = (smp1, smp2),  membership  = bel', 
        osetCard   = cardin,        osetPointed = elem, 
        osetList   = list,          osetBounds  = bounds, 
        osetProps  = props,         osetConstrs = [],     -- so far 
        osetOpers  = []}
  where
  OSet {osetSample = smp1,   membership  = bel1,
        osetCard   = card1,  osetPointed = el1,
        osetList   = ll1,    osetBounds  = _,
        osetProps  = ps1,    osetConstrs = _    } = xX

  OSet {osetSample = smp2,   membership  = bel2,
        osetCard   = card2,  osetPointed = el2,
        osetList   = ll2,    osetBounds  = _,
        osetProps  = ps2,    osetConstrs = _    } = yY

  cardin = case (card1,card2) of (Fin c1,   Fin c2  ) -> Fin (c1*c2)
                                 (Infinity, _       ) -> Infinity
                                 (_,        Infinity) -> Infinity
                                 _                    -> UnknownV
  bel' 'r' (x,y) = bel1 'r' x  &&  bel2 'r' y
  bel' _   _     = True

  elem = case (el1, el2) of 
                (Just Nothing,   _             ) -> Just Nothing
                (_,              Just Nothing  ) -> Just Nothing
                (Just (Just e1), Just (Just e2)) -> Just $ Just (e1, e2)
                _                                -> Nothing
  list = case (ll1, ll2)  
         of 
         (Just xs, Just ys) -> Just [(x, y)| x <- xs, y <- ys]
         _                  -> Nothing
      
  bounds = (Nothing, Nothing, Nothing, Nothing)
  ----------------------------------------------------------------------
  names           = [Finite, FullType, IsBaseSet]
  [fin1, t1, bs1] = fromMaybe (error $ msg "xX\n") $
                                     allMaybes [lookup p ps1 | p<-names]
  msg = showString "\ndirectProduct_set xX yY," . 
        showString "\noSetPointed xX =  " . showsn 1 el1 .
        showString "\noSetPointed yY =  " . showsn 1 el2 .
        showString "\n\nNot all properties listed in  "

  [fin2, t2, bs2] = fromMaybe (error $ msg "yY\n") $
                                   allMaybes [lookup p ps2 | p <- names]
  fin   = and3 fin1 fin2
  ft    = and3 t1   t2
  bs    = and3 bs1  bs2
  props = [(IsBaseSet,      bs ), (Finite, fin),
           (FullType,       ft ),
           (OrderIsTrivial, Yes), (OrderIsTotal, No ), 
           (OrderIsNoether, Yes), (OrderIsArtin,Yes)]


------------------------------------------------------------------------
directProduct_semigroup ::  
                 Subsemigroup a -> Subsemigroup b -> Subsemigroup (a, b)

-- directProduct_semigroup   yields the subsemigroup of the base
-- semigroup of (a,b). Basic operations are inherited from (a,b).
-- Hence H1, H2 must have the same type AddOrMul.

directProduct_semigroup sH1 sH2 =

  Subsemigroup {subsmgType    = opType,  subsmgUnity = unM, 
                subsmgGens    = gens,    subsmgProps = props, 
                subsmgConstrs = [],      subsmgOpers = []}
  where
  (type1, unM1, gens1, props1) = (subsmgType sH1, subsmgUnity sH1, 
                                  subsmgGens sH1, subsmgProps sH1)
  (type2, unM2, gens2, props2) = (subsmgType sH2, subsmgUnity sH2,
                                  subsmgGens sH2, subsmgProps sH2)
  opType = case (type1,type2)  
           of
           (Add, Add) -> Add
           (Mul, Mul) -> Mul
           _          -> error "\ndirectProduct_semigroup sH1 sH2:   \
                               \the semigroups must be of the same\n\
                               \type:  Add or Mul.\n"
  unM = case (unM1, unM2) of 
                (Just (Just u1), Just (Just u2)) -> Just $ Just (u1, u2)
                (Just Nothing,   _             ) -> Just Nothing
                (_,              Just Nothing  ) -> Just Nothing
                _                                -> Nothing
  gens = case (gens1, gens2)  
         of  
         (Just gs1, Just gs2) -> Just [(x, y) | x <- gs1, y <- gs2]
         _                    -> Nothing
  ----------------------------------------------------------------------
  names = [Commutative, IsGroup, IsMaxSubsemigroup, IsCyclicSemigroup]

  [com1, isG1, isMax1, cyc1] = 
               fromMaybe (error "\ndirectProduct_semigroup gG hH:  \
                                \not all properties\nlisted in gG.\n") $ 
                                allMaybes [lookup p props1 | p <- names]
  [com2, isG2, isMax2, cyc2] = 
               fromMaybe (error "\ndirectProduct_semigroup gG hH:   \
                                \not all properties\nlisted in hH.\n") $
                         allMaybes [lookup p props2 | p <- names]

  props = [(IsOrderedSubsemigroup, Unknown           ),  -- ?
           (Commutative,           and3 com1 com2    ),
           (IsGroup,               and3 isG1 isG2    ),
           (IsCyclicSemigroup,     cyc               ),
           (IsMaxSubsemigroup,     and3 isMax1 isMax2)
          ]
  cyc = if (and3 cyc1 cyc2) == No then No  else Unknown  -- so far


------------------------------------------------------------------------
directProduct_group :: 
             (Set a, Set b) =>
             a -> OSet a -> Subgroup a -> b -> OSet b -> Subgroup b -> 
                                                         Subgroup (a, b) 
-- the groups must be of the same operation name

directProduct_group  un1 set1 gG1 un2 set2 gG2 =

 (case (tp1 == tp2, card1, card2)
  of
  (False, _    , _    ) -> 
       error $ 
       showString "\ndirectProduct_group un1 set1 gG1 un2 set2 gG2,\n" $
       showString "un1 = " $ showsn 1 un1 $  
       showString "\nun2 = " $ showsn 1 un2
       "\ngG1, gG2  must be of same operation name.\n"

  (_,     Fin 1, _    ) -> isoGroup f1 if1 gG2
  (_,     _    , Fin 1) -> isoGroup f2 if2 gG1
  _                     ->
                      Subgroup {subgrType    = tp1,  subgrGens  = gens, 
                                subgrCanonic = can,  subgrProps = props,
                                subgrConstrs = [],   subgrOpers = []}
 )
 where
 (tp1, gens1, can1, props1) =
                 (subgrType gG1, subgrGens gG1, subgrCanonic gG1,
                                                         subgrProps gG1)

 (tp2, gens2, can2, props2) = 
                 (subgrType gG2, subgrGens gG2, subgrCanonic gG2, 
                                                         subgrProps gG2)
 (card1,   card2  ) = (osetCard set1,  osetCard set2 )
 (sprops1, sprops2) = (osetProps set1, osetProps set2)
                            -- Below we deal with the case G1,G2 /= {e}, 
                            -- the other case is done separately.
 gens = case (gens1, gens2)  
        of  
        (Just gs1, Just gs2) -> 
                   Just ([(x, un2) | x <- gs1] ++ [(un1, y) | y <- gs2])
        _                    -> Nothing
 can = case (can1, can2) of
                    (Just c1, Just c2) -> Just (\ (x, y)-> (c1 x, c2 y))
                    _                  -> Nothing
 -----------------------------------------------------------------------
                                                  -- forming properties:
 namesS = [Finite, IsBaseSet]
 namesG = [IsCyclicGroup, IsNormalSubgroup, IsMaxSubgroup]
 [fin1, bas1]        = [lookupProp p sprops1 | p <- namesS]
 [fin2, bas2]        = [lookupProp p sprops2 | p <- namesS]
 [cyc1, norm1, max1] = [lookupProp p props1  | p <- namesG]
 [cyc2, norm2, max2] = [lookupProp p props2  | p <- namesG]

 props = [(IsCyclicGroup,     cyc     ), 
          (IsPrimeGroup,      No      ),   -- because G is normal in GxH
          (IsNormalSubgroup,  isNormal), 
          (IsMaxSubgroup,     isMax   ), 
          (IsOrderedSubgroup, Unknown )  -- so far
         ]
                       -- GxH is cyclic <==> 
                       -- both G and H are cyclic and finite and
                       -- have the reciprocally prime cardinalities
 cyc | cyc1 == No || cyc2 ==No ||
       fin1 == No || fin2 == No               = No
     | cyc1 == Unknown  || cyc2 == Unknown ||
       fin1 == Unknown  || fin2 == Unknown    = Unknown
     | otherwise                              =  
         case (card1, card2) of
                      (Fin c1, Fin c2) -> boolToPropV ((gcd c1 c2) == 1)
                      _                -> Unknown

                           -- for the subgroups G,H in the *base groups* 
                           -- G' and H' respectively  
                           -- GxH is normal <==> both G and H are normal
 isNormal = and3 norm1 norm2

                -- GxH is maximal <==> 
                -- one of G,H is the *base group* and another is maximal
 isMax | max1 == No || max2 == No  = No
       | bas1 == Yes               = max2
       | bas2 == Yes               = max1
       | otherwise                 = Unknown
 ------------------------------------------------------------------------
            -- f1,if1,f2,if2  are for the case when G1 or G2 is {e}.
            -- f1: G2 -> {e} x G2    is the isomorphism for the case
            --                       G1 = {e}.  if1 = inverse(f1).
            -- similar are f2,if2.
 f1  g2 = (un1, g2)
 if1    = snd 
 f2  g1 = (g1, un2)
 if2    = fst  


------------------------------------------------------------------------
directProduct_ring :: (Ring a, Ring b) => 
                      a -> Subring a -> b -> Subring b -> Subring (a, b)
directProduct_ring zrA rA           zrB  rB        = 

  Subring {subringChar  = char,   subringGens    = gens, 
           subringProps = props,  subringConstrs = constrs,
           subringOpers = opers}
  where
  Subring {subringChar  = charA,   subringGens    = gensA, 
           subringProps = propsA,  subringConstrs = _,
           subringOpers = _                                } = rA
  Subring {subringChar  = charB,    subringGens    = gensB, 
           subringProps = propsB,   subringConstrs = _,
           subringOpers = _                                } = rB

  char = case (charA, charB)
         of
         (Just ca, Just cb) -> if ca == 0 || cb == 0 then  Just 0
                               else                     Just $ lcm ca cb
         _                  -> Nothing
  gens = 
      case (gensA,gensB)   -- optimizations possible 
      of
      (Just as, Just bs) ->
                     Just ([(a, zrB) | a <- as] ++ [(zrA, b) | b <- bs])
      _                  -> Nothing
  ----------------------------------------------------------------------
                                             -- forming property values:
  names            = [HasNilp, PIR]
  [hasNilpA, pirA] = fromMaybe (error notAllP_msg) $
                                allMaybes [lookup p propsA | p <- names]
  [hasNilpB, pirB] = fromMaybe (error notAllP_msg) $
                                allMaybes [lookup p propsB | p <- names]
  notAllP_msg = 
             showString "\ndirectProduct_ring zrA rA zrB rB," $
             showString "\nzrA = " $ shows zrA $ showString "  <-\n  " $ 
             showsDomOf 1 zrA $ showString "\nzrB =  " $ shows zrB $ 
             showString "  <-\n  " $ showsDomOf 1 zrB
                                  "\nnot all properties listed in  rA\n"
      
  props = [(IsField,       No     ), (HasZeroDiv, Yes),   
           (HasNilp,       hasNilp), (Factorial,  No ), 
           (IsRealField,   No     ),  
           (IsPrimaryRing, No     ), -- (1,0) is a zero divisor
                                     -- and not nilpotent
           (PIR,           pir    ),
           (IsGradedRing,  Unknown),
           (IsOrderedRing, Unknown)  -- so far
          ]
  hasNilp = or3 hasNilpA hasNilpB
                            -- in particular, if  a  is a nilpotent in A
                            -- then  (a,0)  is a nilpotent in  A+B ...
  pir = and3 pirA pirB      -- in particular, if  (a) (+direct) (b) 
                            -- can be generated by  (a,b)  in  A+B
  ----------------------------------------------------------------------
  constrs = []

     {- OLD *****************************************************
    finGenExtConstr = case  (firstFGCons conssA, firstFGCons conssB) of
      (Nothing  , _        ) -> [] (_  , Nothing  ) -> []
      (Just fgcA, Just fgcB) -> []  -- so far
              -- Here should be something like this:
              -- if  A = A'[a1,a2]/Ia,  B = B'[b1,b2]/Ib,  then
              -- A+B =  (A'+B') [(a1,0),(a2,0),(0,b1),(0,b2)] / I, 
              -- where  I = Ia+Ib  (?)
    firstFGCons []        =  Nothing
    firstFGCons (c:conss) =  case  c  of
            (FinGenExt_subring _ _ _ _ _ _ _) -> Just c
            _                                 -> firstFGCons conss
     END OLD *****************************************************
     -}

  --------------------------------------------------------------------
  opers = []
    -- We set this so becaus
    -- * `operations'  might define  Grading, dimOverPrimeField.
    -- * dimOverPrimeField  should be *skipped*.
    --   For it makes sense only when Integer ring image  Z'= F(Z)
    --   for  F(n) = unity*n,  extends to the field inside R. 
    --   And  n -> n*(1,1)  cannot satisfy this.
    -- * Grading  is good when it gets the  *parameters*, the 
    --   weight vectors  u,v  for the components A,B of A+B. 
    --   So that  w((f,g))=  u*w(f)+g*w(g)  would be the weight 
    --   homomorphism: (A+B,mul) -> PowerProduct,
    --   here  u*w(f)  is the scalar product of vectors.
    --   So we skip the grading too. 
    --   It may be added to `operations' by some separate function 
    --   that takes these u,v.

