------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------




-- Residue ring  a[x1..xn] / I :
-- specialization of functor  b -> ResidueI b  to  
-- b = (c-Euclidean factorization ring  a) => ResidueI (Pol a).
--
-- Several instances are added for this case
-- which overlap with the instances for  ResidueI b.
-- See  Manual.'rsi.s',  ResRing_*, ResEuc_*.




module ResPol_ ( -- instances for ..=> ResidueI (Pol a):
                 -- Set, AddSemigroup, Ring
               )
               -- All needed from here is  reexported by  Residue
where
import qualified Data.Map as Map (empty, lookup, insert)

import DPrelude (Length(..), -- class 
                 PropValue(..), InfUnn(..), 
                 not3, and3, boolToPropV, lookupProp, ct, ctr, showsn)
import Categs 
import SetGroup (Set(..), AddSemigroup(..),  zeroS, unity, power, 
                                 isFiniteSet, compareTrivially, neg, sub
                )
import RingModule (Ring(..), LinSolvRing(..), EuclideanRing(..), 
                   FactorizationRing(..),  genFactorizationsFromIdeal, 
                                          isPrimeIdeal, upRing, isField)
import VecMatr  (constVec)
import UPol_    (PolLike(..), lc, lc0)
import Pol_     (Pol(..))
import Pol2_    () -- instance..=> LinSolvRing (Pol a)
import ResEuc0_ (Residue(..))
import QuotGr_  (ResidueG(..))
import ResRing_ (ResidueI(..))
import GBasis   (underPPs    )
import qualified ResRing_  (showsd_, fromexpr_)
import qualified ResRing__ (resRingHasNilp_   )






------------------------------------------------------------------------
-- LOCAL.
-- Build  rC/Ic,  with many auxiliary attributes.

coefResRing (Rsi f iD _) =                                -- Rsi f iD fD

       (zr, un, bProps, gs, canRed, gcs, lpps', c0, isUnity_I, aD, mbC')
 where
 Pol _ c _ vars aD = f
 iI                = fst iD
 (bProps, Just gs) = (idealGenProps iI, idealGens iI)
 (zr, un)          = (zeroS c, unity c)
 canRed            = fst . moduloBasis "cg" gs

       -- (aD2, ftC) = baseFactrRing c aD1; ftrPropsC=fctrRingProps ftC
       -- do we need this ? ****
       -- withIsPrimeC = lookupProp WithIsPrime ftrPropsC
       -- withFactorC  = lookupProp WithFactor  ftrPropsC

 zrPP  = constVec (Vec vars) 0  :: PowerProduct
 gcs   = filter ((== zrPP) . lpp) gs
 lpps  = map lpp gs
 c0    = if  null gcs  then  zr    else  lc $ head gcs
 lpps' = if  null gcs  then  lpps  else  tail lpps
                                               -- recall what are g0, c0
 isUnity_I = not (null gcs)  && (eucNorm c0 == eucNorm un)

                             -- try to extract easy factorization for c0
 ft | c0 == zr                 =  []
    | (isPrimeIdeal iI) == Yes =  [(c0, 1)]
    | otherwise                =
                          case genFactorizationsFromIdeal iI  
                          of
                          Nothing   -> []
                          Just ftzs -> [(lc p, k) | (p, k) <- head ftzs]
                                 -- here the c0 factorization means 
                                 -- factorization of constant polynomial 
 cI = PIRChinIdeal {pirCIBase      = c0,  pirCICover = [],
                    pirCIOrtIdemps = [],  pirCIFactz = ft
                   }
 zr' = Rse zr cI aD    -- :: ResidueE a  ?
                                         -- zr' has sense only for c0/=0
                                                          -- rC' = rC/Ic
 mbC' = if  null gcs || isUnity_I  then  Nothing
        else                             Just $ upRing zr' Map.empty


msgBas = "\n\ngx-basis required in ideal\n"      
                                                    -- overlaps in ghc**
resMsg :: (EuclideanRing a, FactorizationRing a, Ring (ResidueE a)) =>
          String -> ResidueI (Pol a) -> String -> String
resMsg str r =  showString (str ++ " r rdom,\nr = ") .
                showsn 1 r . showString "\n <- D/I =  " . showsDomOf 1 r

------------------------------------------------------------------------
addToResDomIf :: LinSolvRing a =>                               -- LOCAL
                 Properties_IdealGen ->                      -- basProps
                 Domains1 a          ->                      -- aD
                 Domains1 b          ->                      -- rD
                 CategoryName        ->                      -- name
                 Domain1  b          ->                      -- dm
                 c                   ->                      -- dm'
                 String              -> (Domains1 b, c)       -- rD_new
-- example:
-- let  { g = Subgroup {...};  coefDoms = ..;  resDoms = Map.empty}
-- in
-- addToResDomIf basProps coefDoms resDoms AddGroup (D1Group g) g
--                                                     "baseAddGroup"
-- -> (resDomsNew, g      ),  or maybe,  (resDoms, error..)

addToResDomIf bProps aD rD name dm dm' msg =
  case
      (lookup IsGxBasis bProps, Map.lookup EuclideanRing aD) 
  of
  (Just Yes, Just (D1EucR eC)) ->
             case
                 lookup DivRemCan $ eucRingProps eC
             of
             Just Yes -> (Map.insert name dm rD, dm')
             _        -> 
                   (rD, error (msg ++ " (Rsi (Pol..)..) _:\nc-Euclidean\
                                      \ coefficient ring needed.\n"))
  _ -> (rD, error (msg ++ " (Rsi (Pol..)..) _:\ngx-basis required in \
                          \ideal, and a c-Euclidean coefficient ring.\n"
       )          )



------------------------------------------------------------------------
instance (EuclideanRing a, FactorizationRing a, 
          Ring (ResidueE a)                           -- overlaps in ghc
         )
         => Set (ResidueI (Pol a))
  where
  compare_m  = compareTrivially
  showsDomOf = ResRing_.showsd_
  fromExpr   = ResRing_.fromexpr_

  baseSet  r@(Rsi f (_,dm) fD) rdom =
    (case 
         (Map.lookup Set rdom, genLength gcs <= 1, gH_mb)
     of
     (Just (D1Set o), _,     _      ) -> (rdom,o)
     (_,              False, _      ) -> 
                               (rdom, error $ resMsg "baseSet" r msgBas)
     (_,              _,     Nothing) ->
                            (rdom, error $ resMsg "baseSet" r
                                   "\n\nSubgroup not found in ideal.\n")
     _                                ->
                  addToResDomIf bProps aD rdom Set (D1Set o) o "baseSet"
    )
    where
    (zr, _, bProps, _, canRed, gcs, lpps', _, _, aD, mbC') = 
                                                           coefResRing r
    gH_mb              = Map.lookup AddGroup dm
    Just (D1Group gH)  = gH_mb
    (_,   polSet )     = baseSet f fD
    (_,   resGSet)     = baseSet (Rsg f (gH, dm) fD) Map.empty
    (aD1, cSet   )     = baseSet  zr aD
    (_,   rC     )     = baseRing zr aD1
    Just cD'           = mbC'            -- has sense when c0 /= 0
    Just (D1Set c'Set) = Map.lookup Set cD'
    Just (D1Ring rC' ) = Map.lookup Ring cD' 
    belongsPol         = membership polSet
    list               = osetList   resGSet
    finiteUnderPPs pps = case fst $ underPPs pps of Fin _ -> True
                                                    _     -> False
    isFieldC' = case (gcs, mbC') of ([], _     ) -> isField rC
                                    (_,  Just _) -> isField rC'
                                    _            -> No
    bel' 'r' (Rsi h _ _) =  (canRed h) == h  &&  belongsPol 'r' h 
    bel' _   (Rsi h _ _) =  (canRed h) == h

    list' = case list of Nothing -> Nothing                    -- so far
                         Just xs -> Just $ map (ct r . resRepr) xs
    --------------------------------------------------------------------
    props' = [(Finite,         fin'), (IsBaseSet, Yes),   
              (FullType,       No  ),  -- for gH/={0}
              (OrderIsTrivial, Yes ),  -- so far
              (OrderIsTotal,   No  ), 
              (OrderIsNoether, Yes ), (OrderIsArtin, Yes)
             ]                           
                                           -- finding fin' = isFinite(Q)
    finC' = case (gcs, mbC') of ([], _       ) -> isFiniteSet cSet
                                (_,  Nothing ) -> Yes
                                _              -> isFiniteSet c'Set
    fin' = and3 finC' $ boolToPropV $ finiteUnderPPs lpps'
    --------------------------------------------------------------------
                                           -- finding  cardin' = card(Q)
    cardC' = case (gcs, mbC') of ([], _      ) -> osetCard cSet
                                 (_,  Nothing) -> Fin 0
                                 _             -> osetCard c'Set
    cardin' = case (cardC', isFieldC')  
              of
              (Infinity, _  ) -> Infinity
              (Fin 0   , _  ) -> Fin 0
              (Fin crC', Yes) -> case fst $ underPPs lpps'
                                 of
                                 Fin n -> Fin $ power crC' n
                                 _     -> Infinity
              _               -> UnknownV

    o = OSet {osetSample  = r,        membership  = bel', 
              osetCard    = cardin',  osetPointed = Just $ Just r, 
              osetList    = list', 
              osetBounds  = (Nothing, Nothing, Nothing, Nothing),
              osetProps   = props',  
              osetConstrs = [],       
              osetOpers   = []}


------------------------------------------------------------------------
instance (EuclideanRing a, FactorizationRing a, 
          Ring (ResidueE a)                       -- overlaps in ghc
         ) 
         => AddSemigroup (ResidueI (Pol a))  
  where
  zero_m r = Just $ ct  r $ zeroS $ resRepr r
  neg_m  r = Just $ ctr r $ neg   $ resRepr r

  add   x =        ctr x . add (resRepr x) . resRepr
  sub_m x = Just . ctr x . sub (resRepr x) . resRepr

  baseAddSemigroup r rdom =
    (case 
         (Map.lookup AddSemigroup rdom, genLength gcs <= 1)
     of
     (Just (D1Smg s), _    ) -> (rdom,s)
     (_,              False) ->
                      (rdom, error $ resMsg "baseAddSemigroup" r msgBas)
     _                       ->
                               addToResDomIf bProps aD rdom AddSemigroup 
                                          (D1Smg s) s "baseAddSemigroup"
    )
    where
    (zr, _, bProps, _, _, gcs, lpps', _, isUnity_I, aD, mbC') =
                                                           coefResRing r
    zeroQ               = zeroS r
    (_, aSmgC )         = baseAddSemigroup zr aD
    smgCprops           = subsmgProps aSmgC
    Just cD'            = mbC'           -- has sense when c0 /= 0
    Just (D1Smg aSmgC') = Map.lookup AddSemigroup cD'
    underPPNum          = fst $ underPPs lpps'
    smgC'props          = case (isUnity_I, gcs) of 
                                        (True, _ ) -> []
                                        (_,    []) -> smgCprops
                                        _          -> subsmgProps aSmgC'
    --------------------------------------------------------------------
    props' = [(Commutative,           Yes    ), (IsGroup, Yes),
              (IsMaxSubsemigroup,     No     ),
              (IsOrderedSubsemigroup, Unknown), -- so far
              (IsCyclicSemigroup,     cyc'   )
             ]
    cyc' = case (isUnity_I, underPPNum, gcs) 
           of
           (True, _,     _ ) -> Yes
           (_,    Fin 1, []) -> lookupProp IsCyclicSemigroup smgCprops 
           (_,    Fin 1, _ ) -> lookupProp IsCyclicSemigroup smgC'props
           _                 -> No

    s = Subsemigroup {subsmgType    = Add,  
                      subsmgUnity   = Just $ Just zeroQ,
                      subsmgGens    = Nothing, -- so far
                      subsmgProps   = props', 
                      subsmgConstrs = [],
                      subsmgOpers   = []}


------------------------------------------------------------------------
instance (EuclideanRing a, FactorizationRing a, 
          Ring (ResidueE a)                     -- overlaps in ghc**
         ) 
         => Ring (ResidueI (Pol a))
  where
  fromi_m r = fmap (ctr r) . fromi_m (resRepr r)

  baseRing  r@(Rsi f (iI, _) fD)  rD = 
    (case 
         (isUnity_I, rC_mb)
     of
     (True, _      ) -> (rD, error $ resMsg "baseRing" r 
                                        "\n\nResidue by Unity ideal.\n")
     (_,    Nothing) -> (rD, error $ resMsg "baseRing" r
                          "\n\nRing term not found for coefficients.\n")
     _               ->
           addToResDomIf bProps aD rD Ring (D1Ring resR) resR "baseRing"
    )
    where
    (_, _, bProps, _, _, gcs, lpps', _, isUnity_I, aD, mbC') = 
                                                           coefResRing r
    -- below, before `in',  isUnity_I = False

    underPP_num    = fst $ underPPs lpps'
    (rR, zr)       = (snd $ baseRing f fD, zeroS $ sample f)
    Just dC'       = mbC'          -- use it for non-trivial cI
    rC_mb          = Map.lookup Ring aD
    (aC'mb, rC'mb) = (Map.lookup AddSemigroup dC', Map.lookup Ring dC')
    Just (D1Smg aC')  = aC'mb
    Just (Just zrC')  = subsmgUnity aC'
    Just (D1Ring rC ) = rC_mb
    Just (D1Ring rC') = rC'mb
    (propsR, propsC)  = (subringProps rR, subringProps rC)
    opsC              = subringOpers rC
    (charC, fieldC)   = (subringChar rC, isField rC)
    propsI            = idealProps iI      
    basFact           = genFactorizationsFromIdeal iI
    --------------------------------------------------------------------
    (propsC', opsC', charC') = 
                        case mbC' 
                        of
                        Nothing  -> ([], [], Nothing)  
                        _        -> (subringProps rC', subringOpers rC',
                                                       subringChar rC' )
    [fieldC', hasNilpC'] = 
                        [lookupProp p propsC' | p <- [IsField, HasNilp]]
    char' = if null gcs then  charC  else  charC'
                                     -- char( rC[vars]/I ) = char(rC/cI)
    --------------------------------------------------------------------
    props' = completeProps ringAxioms  
               [(IsField,       maxI    ), (HasZeroDiv,    not3 primeI),
                (HasNilp,       hasNilpQ), (IsPrimaryRing, primaryI   ),    
                (PIR,           pirQ    ), (Factorial,     factQ      ),
                (IsOrderedRing, Unknown ), -- so far
                (IsRealField,   Unknown ), --
                (IsGradedRing,  Unknown )
               ]
    completeProps _ ps = ps    --     
    ringAxioms         = []    -- we are not sure we need this ***
    --------------------------------------------------------------------
    hasNilpC = lookupProp HasNilp propsC
    hasNilpQ = case (gcs, hasNilpC, hasNilpC') of
                                             ([], Yes, _  ) -> Yes
                                             ([], _,   _  ) -> hasNilpQ'
                                             (_,  _,   Yes) -> Yes
                                             _              -> hasNilpQ'
                              -- below properties are defined as for
                              -- LinSolvRing a..=> Ring (ResidueI a)
                              -- - Pol specifics ignored
    pirQ  = case (pirR, maxI) of (Yes, _  ) -> Yes
                                 (_,   Yes) -> Yes
                                 _          -> Unknown
    factQ = case (maxI, primeI) of (Yes, _  ) -> Yes
                                   (_,   No ) -> No
                                   _          -> Unknown 
    [factR, pirR] = [lookupProp p propsR | p <- [Factorial, PIR]]
    [maxI, primeI, primaryI] =
               [lookupProp p propsI | p <- [IsMaxIdeal, Prime, Primary]]
    hasNilpQ' = ResRing__.resRingHasNilp_  primeI primaryI factR basFact
    --------------------------------------------------------------------
    ops' = 
          case (lookup WithPrimeField opsC, lookup WithPrimeField opsC')
          of
          (Nothing , _        ) -> []
          (_,        Nothing  ) -> []
          (Just wpC, Just wpC') -> [(WithPrimeField, wp' wpC wpC')]
       
    wp' wpC wpC' = WithPrimeField' {frobenius            = fr',
                                    dimOverPrime         = dimOP',
                                    primeFieldToZ        = toz',
                                    primeFieldToRational = tor',
                                    primitiveOverPrime   = primOP'}
        where
        primOP' = error $ resMsg "baseRing" r
                         "\n\na Primitive element for a field extension\
                         \ is not searched for this case,\nso far.\n"
        (toz', tor') = 
          if null gcs then (primeFieldToZ wpC        . lc0 zr . resRepr,
                            primeFieldToRational wpC . lc0 zr . resRepr
                           )
          else -- rC' = rC/(gc),  rC  Euclidean, 
               -- prime field may be only inside rC
               --
          (primeFieldToZ wpC'        . ctr zrC' . lc0 zr . resRepr,
           primeFieldToRational wpC' . ctr zrC' . lc0 zr . resRepr
          )
        dimOP' = case (fieldC, gcs, dimOverPrime wpC, underPP_num)
                 of
                 (Yes, _ , _,        Infinity) -> Infinity
                 (Yes, _ , UnknownV, _       ) -> UnknownV
                 (Yes, _ , Fin d,    Fin u   ) -> Fin (d*u)
                 (_,   [], UnknownV, _       ) -> UnknownV
                 (_,   [], Infinity, _       ) -> Infinity
                 (_,   [], _,        Infinity) -> Infinity
                 (No,  [], _,        _       ) -> Infinity
                                        -- here a Euclidean rC is not a
                                        -- field and contains a field k,
                                        -- hence dim(rC,k) is infinite
                 _                             ->  
                          case (dimOverPrime wpC', fieldC', underPP_num)
                          of
                          (UnknownV, _,   _       ) -> UnknownV
                          (Infinity, _,   _       ) -> Infinity 
                          (_,        _,   Infinity) -> Infinity 
                          (Fin d,    Yes, Fin u   ) -> Fin (d*u)
                          _                         -> UnknownV

        frMsg = "\n\nFrobenius map here can be built so far only \
                \for the case\n(I restrictedTo C) = {0},  C has \
                                              \finite characteristic.\n"
        fr' = case (gcs, charC)  
              of
              (_:_, _      ) -> error $ resMsg "baseRing" r frMsg
              (_,   Nothing) -> error $ resMsg "baseRing" r frMsg
              (_,   Just 0 ) -> error $ resMsg "baseRing" r frMsg
              (_,   Just p ) -> (flip power p, ppInv')
                        where
                        ppInv' = error $ resMsg "baseRing" r 
                                 "\n\nNo Frobenius-inverse map provided\
                                             \ for this case, so far.\n"
    resR = Subring {subringChar    = char', 
                    subringGens    = Nothing,  -- so far
                    subringProps   = props',
                    subringConstrs = [],       -- so far
                    subringOpers   = ops'}





{- OLD ***********************************************************     

Of Prelude:
(PFact):
  Recently, FinGenExt construction is done only for the case c0 = 0, 
  rC  a prime field. For example,  Q = Z[x]/(5,x^2+2)  is a finite
  field, but recent DoCon would *not* factor over Q.
  To obtain this factorization, use that  Q  is isomorphic to  
  Q' = (Z/(5))[x]/(x^2+2)  and build  Q'  instead. For future:
  If  vars = [_]  (let it be [x]),  g's = [g],  |rC'|=p the prime,
      g  irreducible over rC',
  then the FinGenExt construct prepared by DoCon expresses the 
  finite field extension   rC' -- Q  given by the minimal polynomial
  g,  and the isomorphisms  Q <--> rC'[x]/(g).  These isomorphisms 
  provide the factorization operation for polynomials over Q - see 
  Pol.hs, polFactor_finField. The question of rC' being a prime 
  finite field is again, solved by the ResidueE constructor. 
  The primality of g  over  rC' is determined by first seeing  Prime
  attribute for I, and then, if needed, by applying  isPrime g.
  Example:  for  Q = Z[x]/(5,x^2+2)  <-->  GF(5)[x]/(x^2+2)
      DoCon prepares the factorization for the polynomials over Q. 
Fore advanced constructs may be possible in future.  For example,
we might build here the minimal polynomial and the primitive element
for the tower of algebraic extensions.
--------------------------------------------------------------------
Of implementation:
      -- Build constructions  constrs'.
      -- Case  Ic = {0}  and  rC  is a prime field.
      --   Form the finite algebraic 
      --   extension construction "FinGenExt" of kind 
      --   rC -- Q = rC[vars]/I   (see `Construction_subring').
      --   Here we have to build the embedding-image C' of rC in 
      --   Q;
      --   the generator list for Q over C' is the list  varsQ  of 
      --   the variable polynomial images in Q. The relation ideal  
      --   relI  is the image of I  in  Q[t1,...,tn],  and here we 
      --   put  [t1,...,tn] = vars.
      -- Case   Ic = {0}  and  rC  is not a prime field.
      --   For each listed  FinGenExt  construction  
      --   rC' -- rC  form the FinGenExt construction  rC' -- Q. 
      --   so far, we do not construct the primitive element.
      -- Case  Ic = (c0)  is non-zero, c0 not prime:  constrs'= []
      -- Case  Ic = (c0)  c0 is prime.
      --   Q is isomorphic to  Q' = rC'[vars]/iI',  
      --   iI' = Ideal(g's),  rC' a field.
      --   Build Q' by applying recursively  baseRing f'Res   (!?) 
      --   and map the FinGenExt construct from Q' to Q.
      constrsC = subringConstrs rC      
      varsP    = map (r f) vars      -- variables as elements of R
      varsQ    = [Rsi h iI | h <- varsP]               -- ... of Q
      isBaseCQ = -- if  cI = {0}  then rCQ form a base set iff
                 -- rQ is isomorphic to rC  i.e. all xi <- I
              if  all ((== zeroR).canRed) varsP  then Yes  else No
      rCQ    = subringToResPol iI rC isBaseCQ
      cToQ c = Rsi (canRed (cToPol c cp vars)) iI      -- rC -> Q
      qToC f = let  g = resRepr f                         -- back
               in   if  isZero g  then  zr  else  lc g
      pToPQ f = let (cs,exps) = unzip (polMons f)   -- R-> Q[vars]
                    mons'     = zip (map cToQ cs) exps
                in  Pol mons' fRes cp vars
      pQtoP f = let  (cs,exps) = unzip (polMons f)         -- back
                     mons'     = zip (map qToC cs) exps
                in   Pol mons' c cp vars
      --------------------------------------------------------------
      relI =  -- (trace  "baseRing zeroPQ \n") $
             (gensToIdeal  
              gsPQ gsFactsPQ gsPropsPQ propsRelI (baseRing zeroPQ))
        -- so far, this stands for  polIdealToPolResPolIdeal iI.
        -- Here relI refers to  (baseRing zeroPQ) = Q[vars].
        -- And Q is being constructed! Will this do? 
      gsPQ      = map pToPQ gs
      gsFactsPQ = []   gsPropsPQ = []   propsRelI = []
      constrs' = case (gcs, fieldC')of ([], _  ) -> constrs_i0
                                       (_ , Yes) -> constrs_fieldC'
                                       _         -> []
      constrs_i0 = if  dimOverPrimeC == 1  
         then         
          [(FinGenExt_subring "" rCQ varsQ relI propsI toP fromP)]
                                -- recall that propsI refer to the
                                -- properties of  relI  over rCQ
        else  liftConstrs constrsC
             where  toP=pToPQ.fromPRes;  fromP f=Rsi (pQtoP f) iI
      liftConstrs []       = []
      liftConstrs (ct:cts) = (lcon ct)++(liftConstrs cts)
      lcon (FinGenExt_subring ('r':_) _   _    _  _      _ _) = []
      lcon (FinGenExt_subring _       rC' gens iJ propsJ _ _) = []
                                                         -- so far
           -- Finish this. We will also need here
           -- finding of primitive element ...
      lcon _                                                  = []
      constrs_fieldC' = []   -- so far
       {- future ****
        let  (Just rC')  = mbC';     zr'= zeroFromSubring rC'
          un' = unity zr';     canRedEuc x = eucRem 'c' x c0
          toOverC' (Pol mons c cp vars) =
                 let  (cs,exps) = unzip mons; c's = map canRedEuc cs
                 in   Pol (zip c's exps) zr' cp vars
          f'     = toOverC' f;  g's    = map toOverC' (tail gs)
          iI'    = gensToIdeal_syz g's fctrs' bProps propsI
          fctrs' = []  --?          
       constrsOverC'= subringConstrs $ baseRing_r (Rsi f' iI')
        in ...
       -}
END OLD ************************************************************
-}
