------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------




 

module Pol1_              -- Polynomial constructor. Several instances.
                          -- All needed from here is reexported by  Pol.
  (PPCoefRelationMode(..),
   toPolOverPol, fromPolOverPol, polSubst, polValueInCommRing, 
   set_, asmg_, agr_, msmg_  -- local
   -- , instances for Pol: 
   --  Length(..), Show, DShow, Random, Set, AddSemigroup, AddMonoid, 
   --  AddGroup, MulSemigroup, MulMonoid, Ring, CommutativeRing
  )
where
import System.Random (Random(..))      -- non-standard, non-GHC

import qualified Data.Map as Map (empty, lookup, insert)

import Data.Maybe (catMaybes )
import Data.List  (genericDrop, genericSplitAt)

import DPrelude (Length(..), DShow(..), -- classes 
                 Natural, MMaybe, PropValue(..), Expression(..), 
                 InfUnn(..),  tuple31, tuple32, tuple33, allMaybes, 
                 sum1, ct, ctr, zipRem, sum1byBinary, showsn)
import Categs
import SetGroup 
import RingModule
import VecMatr (vecSize)
import UPol_   (PolLike(..), -- class 
                PPOrdTerm,  lc, lc0, upolMons, ppoComp, lexPPO, cPMul
               )
import Pol_ (Pol(..), polPPComp, polMons, reordPol, headVarPol, 
                                                    addVarsPol, cToPol)
import qualified UPol0_ (pshowsd_)
import qualified Pol__  (shows_)
import qualified Pol_   (neg_, add_, mul_, times_)






-----------------------------------------------------------------------
instance Length (Pol a) where  genLength = genLength . polMons

instance Ring a => Show  (Pol a) where showsPrec _ = showsn 0 
instance Ring a => DShow (Pol a) where dShows      = Pol__.shows_ 

instance (CommutativeRing a, Random a) => Random (Pol a)  
  where
  -- Random polynomial  f  distributed uniformly in the 
  -- "segment between polynomials  l  and  h"  is put to have random 
  -- coefficients coef(pp)  between  coef(pp,l), coef(pp,h)
  -- for all the power products pp  such that  
  --                           coef(pp,l) /= 0  or  coef(pp,h) /= 0.
  -- Example:
  -- polynomials from      rands (3*x^4*y^3 +2*x*y -2, x*y^2 -x*y) g
  -- may have the coefficients
  --         a <- [0 ..3]  for pp = [4,3],  b <- [0 ..1]  for [1,2],
  --         c <- [-1..2]  for      [1,1],  d <- [-2..0]  for [0,0],
  --         and  0  - for all other power products  pp.

  randomR (l, h) g =  (ctr l $ zip cs pps, g')                  
    where
    (zr, cp) = (zeroS $ sample l, polPPComp l)
    tripls   = mergeMons (polMons l) (polMons h)
                                                -- join monomials of l,h 
                                                -- pairing coefficients
    mergeMons []             mons'      = [(zr, a, p) | (a, p) <- mons']
    mergeMons mons           []         = [(a, zr, p) | (a, p) <- mons ]
    mergeMons ((a, p): mons) ((b, q): mons') = 
           case 
               cp p q  
           of
           EQ -> (a,  b,  p): (mergeMons mons mons') 
           GT -> (a,  zr, p): (mergeMons mons           ((b, q): mons'))
           LT -> (zr, b,  q): (mergeMons ((a, p): mons) mons'          ) 

    (ls, hs)     = (map tuple31 tripls, map tuple32 tripls)
    pps          = map tuple33 tripls
    (Vec cs, g') = randomR (Vec ls, Vec hs) g 

  random _ = error "\nrandom  for (Pol ..):   use  randomR  instead.\n"   


------------------------------------------------------------------------
instance CommutativeRing a => Set (Pol a)  
  where
  showsDomOf = UPol0_.pshowsd_
  fromExpr   = fromexpr_ 
  compare_m  = compareTrivially

  baseSet  f@(Pol _ c ord vars aDom)  dom =
                               set_ (showsDomOf 1 f "") dom aDom f bel'
                                          -- (showsDomOf c $ show vars)
    where
    (z, cp) = (zeroS c, ppoComp ord)
    bel' md (Pol mons' _ ord' vars' _) =    -- membership for a[x1..xn]
      let  
        (l, cp') = (genLength vars, ppoComp ord')
        ((coefs, pps), (_, aS)) = (unzip mons', baseSet c aDom)
        bel                     = membership aS
        bl =  if md == 'r' then  all (bel 'r')  else  const True
      in
      vars == vars'  &&  all (/= z) coefs
      &&  all (== l) (map vecSize pps)
      &&  orderedBy cp pps  &&  orderedBy cp' pps  &&  bl coefs
                 where  
                 orderedBy _    []         = True 
                 orderedBy _    [_]        = True
                 orderedBy comp (p: q: ps) = 
                              (comp p q) == GT && orderedBy comp (q: ps)

------------------------------------------------------------------------
set_ :: String                -> 
        Domains1 (p a)        -> 
        Domains1 a -> p a     -> 
        (Char -> p a -> Bool) ->  (Domains1 (p a), OSet (p a))

set_ pDomString dom aD sampleP bel =          -- reused in  RPol, SymPol
  (case  
       (Map.lookup Set dom, Map.lookup AddSemigroup aD)
   of
   (Just (D1Set s), _              ) -> (dom, s)
   (_,              Just (D1Smg aS)) -> pset $ isGroup aS
   _                                 -> (dom, error$ msg msg')
  ) 
  where
  msg = showString ("\nbaseSet sampleP pDom,\nsampleP <-  " ++
                                                            pDomString)
  msg' = "\n\nSet, AddSemigroup  terms must present in the \
         \coefficient domain,\nand the latter must possess \
                                                    \(IsGroup, Yes).\n"
  pset Yes = (Map.insert Set (D1Set s) dom, s)
  pset _   = (dom, error $ msg msg')

  s = OSet {osetSample  = sampleP,       
            membership  = bel,
            osetCard    = Infinity,    
            osetPointed = Just $ Just sampleP,
            osetList    = Nothing,
            osetBounds  = (Nothing, Nothing, Nothing, Nothing),
            osetProps   = props,
            osetConstrs = [],           
            osetOpers   = []
           }
  props = [(Finite,       No ), (IsBaseSet,      Yes),
           (FullType,     No ), (OrderIsTrivial, Yes),
           (OrderIsTotal, No ), (OrderIsNoether, Yes), 
           (OrderIsArtin, Yes)]


------------------------------------------------------------------------
instance CommutativeRing a => AddSemigroup (Pol a)  
  where
  add       = Pol_.add_
  zero_m f  = Just $ ctr f $ zeroS $ sample f
  neg_m     = Just . Pol_.neg_ 
  times_m f = Just . (Pol_.times_ times f)

  baseAddSemigroup  f@(Pol _ c _ _ aD) dom =  
                           asmg_ 
                            (showsDomOf 1 f "") dom aD (ctr f $ zeroS c)


asmg_ :: String -> Domains1 (p a) -> Domains1 a -> p a ->
                                    (Domains1 (p a), Subsemigroup (p a))

asmg_ pDomString dom aD zeroP =              -- re-used in  RPol, SymPol
  (case
       (Map.lookup AddSemigroup dom, Map.lookup AddSemigroup aD)
   of
   (Just (D1Smg s), _              ) -> (dom, s)
   (_,              Just (D1Smg aS)) -> semig aS
   _                                 -> (dom, error $ msg msg')
  )
  where 
  msg = showString ("\nbaseAddSemigroup sampleP pDom,\nsampleP <-  "
                                                       ++ pDomString)
  msg' = "\n\nAddSemigroup  term must present in the " ++
         "coefficient domain, \nwith  (IsGroup,Yes).\n"

  semig aS = case isGroup aS  
             of
             Yes -> (Map.insert AddSemigroup (D1Smg s) dom, s)
             No  -> (dom, error$ msg msg')

  s = Subsemigroup 
             {subsmgType    = Add,      subsmgUnity = Just $ Just zeroP,
              subsmgGens    = Nothing,  subsmgProps = props,
              subsmgConstrs = [],       subsmgOpers = []
             }
  props = [(Commutative,           Yes    ), 
           (IsGroup,               Yes    ),
           (IsMaxSubsemigroup,     No     ), 
           (IsCyclicSemigroup,     No     ),  
           (IsOrderedSubsemigroup, Unknown)]


------------------------------------------------------------------------
instance CommutativeRing a => AddMonoid (Pol a)
instance CommutativeRing a => AddGroup (Pol a)
  where
  baseAddGroup  f@(Pol _ c _ _ aDom) dom = 
                     agr_ (showsDomOf 1 f "") dom aDom (ctr f $ zeroS c)


agr_ :: String -> Domains1 (p a) -> Domains1 a -> p a -> 
                                        (Domains1 (p a), Subgroup (p a))
  
agr_ pDomString dom aD zeroP =               -- reused for  RPol, SymPol
  (case
       (Map.lookup AddGroup dom, Map.lookup AddSemigroup aD)
   of
   (Just (D1Group g), _              ) -> (dom, g)
   (_               , Just (D1Smg aS)) -> gr aS 
   _                                   -> (dom, error $ msg msg')
  )
  where
  msg = showString ("\nbaseAddGroup sampleP pDom,\nsampleP <-  " ++
                                                             pDomString)
  msg' = "\n\nAddSemigroup  term must present in the \
                           \coefficient domain,\nwith  (IsGroup,Yes).\n"
  gr aS = case isGroup aS of
                         Yes -> (Map.insert AddGroup (D1Group g) dom, g)
                         _   -> (dom, error $ msg msg')
  g = Subgroup 
              {subgrType    = Add,                 subgrGens  = Nothing,
               subgrCanonic = Just $ const zeroP,  subgrProps = props,
               subgrConstrs = [],                  subgrOpers = []
              }
  props = [(IsCyclicGroup,     No     ), (IsNormalSubgroup, Yes),
           (IsMaxSubgroup,     No     ), (IsPrimeGroup,     No ),
           (IsOrderedSubgroup, Unknown)]


------------------------------------------------------------------------
instance CommutativeRing a => MulSemigroup (Pol a)   
  where
  mul       = Pol_.mul_
  unity_m f = fmap (ct f) $ unity_m $ sample f

  inv_m f = if  isZero f || not (pIsConst f)  then  Nothing
            else                              fmap (ct f) $ inv_m $ lc f

  divide_m f g = let zeroP = zeroS f
                 in
                 case (f == zeroP, g == zeroP)
                 of
                 (True, _   ) -> Just zeroP  
                 (_,    True) -> Nothing
                 _            -> let (q, r) = pDivRem f g  
                                 in   
                                 if isZero r then  Just q  else  Nothing
  divide_m2 _ _ = error 
                  "\ndivide_m2 (Pol ..) _:  use  divide_m  instead.\n"
  root _ _      = error "\nroot _ (Pol ..) _:  it is not defined for \
                                   \multivariate polynomials, so far.\n"
  -- power  is the default
  ----------------------------------------------------------------------
  baseMulSemigroup  f@(Pol _ c _ _ aD) dm = 
                                    msmg_ (showsDomOf 1 f "") dm aD unpM
              where
              unpM = case  unity_m c  of  Just u -> Just $ Just $ ct f u
                                          _      -> Nothing


msmg_ :: String -> Domains1 (p a) -> Domains1 a -> MMaybe (p a) -> 
                                    (Domains1 (p a), Subsemigroup (p a))
msmg_ pDomString dom aD unpM =          -- re-used in instance for  RPol
  case  
      Map.lookup MulSemigroup dom  
  of
  Just (D1Smg s) -> (dom, s)
  _              ->
    (case catMaybes 
             [Map.lookup nm aD | nm <- [AddSemigroup, MulSemigroup]]
     of
     [D1Smg aAS, D1Smg aMS] -> semig (subsmgProps aAS) (subsmgProps aMS)
     _                      -> (dom, error $ msg msg')
    )
    where
    msg = showString ("\nbaseMulSemigroup sampleP pDom,\nsampleP <-  "
                                                         ++ pDomString)
    msg' = "\n\nAddSemigroup, MulSemigroup terms must present \
                                         \ in the coefficient domain.\n"
    msg'' = "\n\nCommutative ring required for coefficients.\n"

    semig aASProps aMSProps =
      case 
          (lookup IsGroup aASProps, lookup Commutative aMSProps)
      of
      (Just Yes, Just Yes) -> (Map.insert MulSemigroup (D1Smg s) dom, s)
      _                    -> (dom, error $ msg msg'')

    s = Subsemigroup {subsmgType    = Mul,      subsmgUnity = unpM,
                      subsmgGens    = Nothing,  subsmgProps = props,
                      subsmgConstrs = [],       subsmgOpers = []
                     }
    props = [(IsMaxSubsemigroup,     No     ), 
             (Commutative,           Yes    ), 
             (IsGroup,               No     ),
             (IsCyclicSemigroup,     Unknown),
             (IsOrderedSubsemigroup, Unknown)]


------------------------------------------------------------------------
instance (CommutativeRing a, MulMonoid a) => MulMonoid (Pol a)

instance CommutativeRing a => Num (Pol a)  
  where 
  negate = neg
  (+)    = add
  (-)    = sub  
  (*)    = mul
  signum      _ = error "\nsignum (Pol ..):   it is senseless.\n"
  abs         _ = error "\nabs (Pol ..):   it is senseless.\n"
  fromInteger _ = 
             error "\nfromInteger  to (Pol ..):   use  fromi  instead.\n"

instance CommutativeRing a => Fractional (Pol a)  
  where
  (/) = divide
  fromRational _ = error "\nfromRational  to (Pol ..):  instead use\
                         \  fromi  combined with  divide_m.\n"

instance CommutativeRing a => Ring (Pol a) 
  where
  fromi_m f = fmap (ctr f) . fromi_m (sample f)

  baseRing f fdom = 
    (case
         (Map.lookup Ring fdom, dom f)
     of
     (Just (D1Ring r), _ ) -> (fdom, r)
     (_              , aD) ->
            rg (Map.lookup AddSemigroup aD, Map.lookup MulSemigroup aD,
                                                    Map.lookup Ring  aD)
    )
    where
    (zr, pDomString) = (zeroS $ sample f, showsDomOf 1 f "")

    rg (Just (D1Smg addS), Just (D1Smg mulS), Just (D1Ring aR)) =
                                                        rg' addS mulS aR
    rg _                                      = (fdom, error $ msg msg')

    msg = showString ("\nbaseRing sampleP pDom,\nsampleP <-  " ++ 
                                                             pDomString)
    msg' = "\n\nRing or subsemigroup terms not found \
                                           \in the coefficient domain\n"
    msg'' = "\n\nAddSemigroup, MulSemigroup terms  aS, mS  must \
            \reside\nin the coefficient domain,\naS  with  \
            \(IsGroup, Yes),  mS  with  (Commutative, Yes).\n"
    msgPropsSkipped =
            "\n\nSome property names skipped in the coefficient ring.\n"

    rg' addS mulS aR = 
      (case (isGroup addS, isCommutativeSmg mulS) 
       of                                      -- test partially Ring(a)
       (Yes, Yes) -> (Map.insert Ring (D1Ring r) fdom, r)
       _          -> (fdom, error $ msg msg'')
      )
      where
      r = Subring {subringChar  = charC,   subringGens   = Nothing,
                   subringProps = props',  subringConstrs= constrs',
                   subringOpers = opers'}
      constrs' = []  
                  -- do we need explicit FinGenExt construction for Pol?

      (charC, propsC, opersC) =
                      (subringChar aR, subringProps aR, subringOpers aR)
                        --
                        -- possibility:  aRP = baseRingToPolSubring v aR
                        -- - coefficient subring inside  P = R[vars]...
      props' = 
       let
         names = [IsField, HasZeroDiv, HasNilp, IsPrimaryRing, 
                                                              Factorial]
         propVs = case  allMaybes [lookup p propsC | p <- names]  
                  of
                  Just xs -> xs
                  Nothing -> error $ msg msgPropsSkipped

         [field, hasZD, hasNilp, primary, fact] = propVs

         ringAxioms         = []   -- so far
         completeProps _ ps = ps   --

         pir' = if field == No then No else Unknown
                                           -- for it is multivariate
         primary' = primary   -- Lemma...
       in
       completeProps ringAxioms
               [(IsField      , No     ), (HasZeroDiv   , hasZD   ),
                (HasNilp      , hasNilp), (IsPrimaryRing, primary'),
                (Factorial    , fact   ), (PIR          , pir'    ), 
                (IsRealField  , No     ), (IsOrderedRing, Unknown ), 
                (IsGradedRing , No     )  -- so far
               ]

      opers' = 
        case  lookup WithPrimeField opersC  
        of
        Nothing -> []
        Just wp -> [(WithPrimeField, wp')]
          where
          wp' = WithPrimeField' {frobenius            = fr',
                                 dimOverPrime         = Infinity,
                                 primeFieldToZ        = toz',
                                 primeFieldToRational = tor',
                                 primitiveOverPrime   = error msg 
                                }
          msg  = "primitiveOverPrime  not defined for Pol  "++
                                                     "(unlike UPol) \n"
          msgFrobChar = "the Frobenius map for R[x1..xn]:  char(R) > 0\
                                                           \needed.\n"
          toz' = primeFieldToZ wp        . lc0 zr 
          tor' = primeFieldToRational wp . lc0 zr
          fr' = 
            let (pp, ppInv) = frobenius wp
            in
            case charC  
            of
            Nothing -> error msgFrobChar
            Just 0  -> error msgFrobChar
            Just p  -> (pp',ppInv')
              where
              pp' g = ctr f [(pp c, fmap (* p) e) | (c, e) <- polMons g]

              ppInv' g = 
                let 
                  (cs, es) = unzip $ polMons g
                  ps       = 
                      [unzip [quotRem j p | j <- js] | Vec js <- es]
                  (qs, rs) = unzip [(Vec is, Vec js) | (is, js) <- ps]
                  isZeroPP = all (== 0) . vecRepr
                in
                if  any (not . isZeroPP) rs  then  Nothing  
                else                     -- more precise: Just Nothing ?
                case allMaybes $ map ppInv cs
                of
                Nothing  -> Nothing
                Just cs' -> case allMaybes cs' 
                            of
                            Just bs -> 
                                      Just $ Just $ ct f $ zip bs qs
                            _       -> Nothing 


------------------------------------------------------------------------
instance CommutativeRing a => CommutativeRing (Pol a)


------------------------------------------------------------------------
polValueInCommRing :: (CommutativeRing a, CommutativeRing r) => 
                                   Char -> (a -> r) -> [r] -> Pol a -> r 
                                -- mode    cMap        rs     f
-- Value of  f  in the given commutative ring
-- (a more generic variant of substitution in a polynomial): 
-- map coefficients in  f  by  cMap
-- and return the result expression in  r  for the substitution  
--                x(i) := r(i),  x(i) <- xs = pVars f,  r(i) <- rs.
--
-- It must hold  |xs| <= |rs|,  and the remainder of  rs  is ignored.
-- mode = 'l'            means f has the  lexComp ordering - the
--                       evaluations would be somewhat cheaper,
--        other letter   means the generic case.
-- METHOD.
-- f is converted recursively to  R[x2..xn][x1]  and so on,  and the 
-- Horner scheme of substitution is applied by each  xi.

polValueInCommRing mode cMap rs f =    
  (case  
       zipRem rs vars
   of
   (_,     _, _: _) -> 
                   error $ message0 "not enough values for variables.\n"
   (pairs, _, _   ) -> case mode 
                       of 
                       'l' -> subst (map fst pairs) vars f
                                    -- used  rs
                       _   -> subst (map fst pairs) vars $ reordPol o' f
  )
  where
  message0 = showString "\npolValueInCommRing " . shows mode . 
             showString " cMap\n " . showsn 1 rs . showString "\n " . 
             showsn 1 f . showString "\n:\n"
  vars = pVars f
  o'   = lexPPO $ genLength vars
  ----------------------------------------------------------------------
  -- subst  considers (local)  f  in the lexComp order and in the
  -- current Tail variable list  vs.

  subst _       []      f = error $ message0 $ concat
                            ["subst  reduced to empty variable list,\n",
                             "the remaining  f  is\n", showsn 1 f ".\n"]
  subst (r: rs) (_: vs) f = 
    if 
      isZero f  then  cMap $ zeroS $ sample f  -- 0 in r
    else
    case (pIsConst f, vs)  
    of
    (True, _ ) -> cMap $ lc f
    (_   , []) -> sum1 $ zipWith (\ a p -> (cMap a)*p) cs rPowers
                  where                       -- f has become univariate
                  (cs, exps) = unzip $ polMons f
                  js         = map (head . vecRepr) exps 
                                       -- fh = c1*x^j1 +..+ ck*x^jk,
                                       -- so [r^j1 .. r^jk] to be formed
                  rPowers = powersOfOne js r

    _ -> sum1 $ zipWith (*) csr $ powersOfOne js r     
         where
         (cs, js) = unzip $ upolMons $ headVarPol Map.empty f
                                                 -- here ci <- R[x2..xn]
         csr = map (subst rs vs) cs


{- reserve for tesing ------------------------------------------
polValueInCommRingTest ::
          (Ring a, CommutativeRing r) => (a -> r) -> [r] -> Pol a -> r 
polValueInCommRingTest cMap rs f =  
  (case   zipRem rs (pVars f)   of   (pairs, _, []) -> 
                sum1 (zeroR: (map (mapMon (map fst pairs)) $ polMons f))
   _ -> error $ message0 "not enough values for variables.\n"
  )  where zeroR    = zeroS $ cMap $ sample f
  message0 = showString "\npolValueInCommRingTest cMap\n " . shows rs . 
             showString "\n " . shows f . showString "\n:\n"
  mapMon rs (a, Vec js) =  product1 ((cMap a): (zipWith power rs js))
-}


polSubst :: CommutativeRing a => 
                          Char -> Pol a -> [Pol a] -> [[Pol a]] -> Pol a
                       -- mode    f        gs         powerLists

-- Use better  polValueInCommRing ***
--            
-- Substitute polynomials  gs = [g1..gm],  gi <- R[x1..xn],  for the
-- variables x1..xm  in polynomial  f <- R[x1..xn].
-- The rest of xi  remain. If m > n then the rest of gi are ignored.
-- METHOD.
-- f converts recursively to  R[x2..xn][x1]  etc.,  and the Horner 
-- scheme of substitution is applied by each  xi.
-- mode = 'l'            means f has the  lexComp ordering - the
--                       evaluations would be somewhat cheaper,
--        other letter   means the generic case.
-- powerLists  is either  []  or  [g1Powers..gkPowers], 
-- where 
-- giPowers  is either  []  or the infinite list  [gi^2, gi^3 ..].
-- powersLists = []   means the powers are not listed at all, 
--                    compute them by the Horner scheme.
-- giPowers       are ignored for  i > m.
-- k < m          means  giPowers = []  for  i > m.
-- giPowers = []  means again to compute gi^j  by the Horner scheme.

polSubst  mode  f@(Pol _ _ o vars dA)  gs  powerLists =    
  let
    o'  = lexPPO $ genLength vars
    pss = map snd $ zip gs powerLists   -- cut extra ones
    --------------------------------------------------------------------
                                     -- here j1>j2>..>jk >= 0  in js
    powers js []      g = powersOfOne js g
    powers js ([]: _) g = powersOfOne js g
    powers js (ps: _) g = reverse $ pp (reverse js) ps
                     where
                     pp []     _  = []
                     pp (0:js) ps = (unity g):(pp js ps)
                     pp (1:js) ps = g:(pp js ps)
                     pp (j:js) ps = let p:ps' = genericDrop (j-2) ps
                                        js'   = [i+1-j | i <- js]
                                    in  p: (pp js' ps')
    --------------------------------------------------------------------
    -- subst  considers (local) f  in the lexComp order and in the
    -- current Tail variable list  vs:   vars = vars'++vs. 
    -- vars' is accumulated to return the result to vars. |pss| <= |gs|.
    subst []    _   vars' _      f = addVarsPol 'h' o' (reverse vars') f
    subst (g:gs) pss vars' (v:vs) f = 
      case (pIsConst f, vs)  
      of
      (True, _ ) -> addVarsPol 'h' o' (reverse vars') f
      (_   , []) -> let                       -- f became univariate
                       (cs, exps) = unzip $ polMons f
                       js        = map (head . vecRepr) exps 
                                     -- fh = c1*x^j1 +..+ ck*x^jk,
                                     -- so [g^j1..g^jk] to be formed
                       powersG = powers js pss g    
                    in sum1 $ zipWith cPMul cs powersG
      _          -> 
        let (cs, js) = unzip $ upolMons $ headVarPol Map.empty f
                                             -- here ci <- R[x2..xn]
            powersG = powers js pss g     
            pss'    = if  null pss  then []  else tail pss
            csg     = map (subst gs pss' (v:vars') vs) cs
            Pol ms c o vs' _ = sum1 $ zipWith Pol_.mul_ csg powersG
        in  Pol ms c o vs' dA
  in
  if mode == 'l' then  subst gs pss [] vars f
  else             reordPol o $ subst gs pss [] vars $ reordPol o' f


------------------------------------------------------------------------
fromexpr_ :: CommutativeRing a => 
                          Pol a -> Expression String -> ([Pol a],String)
-- LOCAL.
-- Parse polynomial given a sample polynomial and expression.
-- So far, it requires a ring `a' with UNITY.

fromexpr_ smp e = 
  case 
      (unity $ sample smp, pVars smp) 
  of
  (u, vars) -> rd e
    where
    rd e = 
      case fromExpr u e  
      of                            -- first try to parse to coefficient
      ([c], "") -> ([ctr smp c], "")
      _         -> 
        (case e 
         of
         E (L "-") []   [e2] -> rd' "-u" ([],"") (rd e2)
         E (L "-") [e1] [e2] -> rd' "-"  (rd e1) (rd e2)
         E (L "+") [e1] [e2] -> rd' "+"  (rd e1) (rd e2)
         E (L "*") [e1] [e2] -> rd' "*"  (rd e1) (rd e2)
         E (L "/") [e1] [e2] -> rd' "/"  (rd e1) (rd e2)
         E (L "^") [e1] [e2] -> pw (rd e1) (fromExpr (1 :: Integer) e2)
         L s                 -> variable s (span (/= s) vars)
         _                   -> ([], msg "\n\nWrong expression\n")
        )
        where
        msg = showString "\nfromExpr samplePol expr,\nsamplePol =  " . 
              showsn 1 smp . showString "\n <-  " . showsDomOf 1 smp . 
              showString "\nexpr =  " . showsn 1 e 

        rd' "-u" _         ([f], "") = ([-f ], "")
        rd' "-"  ([f], "") ([g], "") = ([f-g], "")
        rd' "+"  ([f], "") ([g], "") = ([f+g], "")
        rd' "*"  ([f], "") ([g], "") = ([f*g], "")
        rd' "/"  ([f], "") ([g], "") = 
                   case divide_m f g  
                   of
                   Just q -> ([q], "")
                   _      -> ([], msg "\n\nFailed to divide with `/'\n")

        rd' _    ([_], "") pair      = pair
        rd' _    pair      _         = pair

        pw ([f], "" ) ([n], "" ) = ([f^n], "" )
        pw ([_], "" ) (_  , msg) = ([]   , msg)
        pw (_  , msg) ([_], "" ) = ([]   , msg)
 
                           -- read monomial polynomial from variable
        variable s (_,  [] ) = 
                  ([], 
                   msg $ ("\n\nVariable "++) $ shows s "  not in list\n"
                  )
        variable _ (vs, vs') = let ns  = (map (const 0) vs) :: [Integer]
                                   ns' = 1:(map (const 0) (tail vs'))
                                   p   = Vec (ns ++ ns')
                                in
                                ([ct smp (u, p)], "")

------------------------------------------------------------------------
data PPCoefRelationMode = HeadPPRelatesCoef | TailPPRelatesCoef
                                          deriving (Eq, Ord, Enum, Show)

toPolOverPol :: CommutativeRing a => PPCoefRelationMode ->      -- mode
                                     Natural            ->      -- n
                                     PPOrdTerm          ->      -- coefO
                                     PPOrdTerm          ->      -- ppO
                                     Pol a              ->      -- f
                                     Pol (Pol a)

-- Embed f from  a[xs]  to  a[ys][zs],  if mode = HeadPPRelatesCoef,
--                   or to  a[zs][ys],  otherwise,
-- where
-- xs = ys ++ zs  = pVars f,  n = length ys.
--
-- coefO and ppO  is the pp-ordering for the coef-part and the power-
-- product part in  a[coefVars][pVars]  respectively.
-- The  new domain bundles are supported as  upRing.

toPolOverPol mode n coefO ppO f =

  (if  n < 1 || n >= (genLength xs)  then
        error $ concat
        ["\ntoPolOverPol ", shows mode " ", shows n " oCoef oPP\n ",
         showsn 1 f  "\n:\nit must hold  1 < n < |pVars f|.\n"
        ]
  else  sum1byBinary ((zeroS unYZ) : (map convertMon $ polMons f))
  )
  where
  xs          = pVars f
  (xs', xs'') = genericSplitAt n xs
  (ys,  zs  ) = case mode of HeadPPRelatesCoef -> (xs',  xs'')
                             _                 -> (xs'', xs' )
                                                         -- ys --> coefs
  un   = unity $ sample f
  unY  = cToPol coefO ys (dom f) un    -- 1 of a[ys]
  dY   = upRing unY Map.empty          -- a[ys]
  unYZ = cToPol ppO zs dY unY          -- 1 of a[ys][zs]

  convertMon (a, Vec ks) =  ctr unYZ (ctr unY (a, Vec ksY), Vec ksZ)
            where
            (ks', ks'') = genericSplitAt n ks
            (ksY, ksZ ) = case mode of HeadPPRelatesCoef -> (ks',  ks'')
                                       _                 -> (ks'', ks' )


------------------------------------------------------------------------
fromPolOverPol ::
                 CommutativeRing a =>
                 PPCoefRelationMode -> PPOrdTerm -> Pol (Pol a) -> Pol a
                 -- mode               ppo          f

-- Embed from  a[xs][ys]  to  a[xs ys],  if  mode = HeadPPRelatesCoef
--                     or to  a[ys xs],  otherwise.
-- ppo  is the pp-ordering for the result.

fromPolOverPol mode ppo f =
                      
  sum1byBinary ((zeroS unXY) : (map convertMon $ polMons f))
  where
  un = sample $ sample f
  ys = pVars f
  xs = pVars $ sample f
  zs = case mode of HeadPPRelatesCoef -> xs ++ ys
                    _                 -> ys ++ xs

  unXY = cToPol ppo zs (dom $ sample f) un

  convertMon (xPol, Vec ks) =
                 reordPol ppo $
                 ct unXY [(a, Vec (join js ks)) | (a, Vec js) <- mons]
                 where
                 mons       = polMons xPol
                 join xs ys = case mode of HeadPPRelatesCoef -> xs ++ ys
                                           _                 -> ys ++ xs





{- reserve ************************************************************

instance (Convertible a b, Ring b) => Convertible a (Pol b)   
  where cvm a f = case cvm a (sample f) of  Just c-> Just $ ctr f c
                                            _     -> Nothing
instance (Convertible a b,AddGroup b)=> Convertible (UPol a) (Pol b)
  where  cvm (UPol mons a v _) (Pol _ b ord vars dom') =
    -- univariate f  is convertible to multivariate  g  iff 
    --   v = pHeadVar f  belongs to  vars = pVars g  and
    --   upolCoef(f)  is convertible to  polCoef(g)
    -- In this case, to convert f to g  means to 
    -- convert coefficient in each monomial removing the obtained 
    --   zero monomials, 
    -- find the position i of v in vars,
    -- convert each exponent j to the PowerProduct pj(i) having j
    --   in position i and 0 in others,
    -- order the monomials with  ord  from  g.
    case  (zeroS b, cvm a b, span (/=v) vars)
    of( _, Nothing, _          ) -> Nothing
      ( _, _      , (_ ,[]   ) ) -> Nothing
      ( z, _      , (vs,_:vs') ) -> 
                     Just (reordPol ord (Pol monsC b ord vars dom'))
        where
        monsC = filter ((/=z).fst) [(cv a b,convExp p)| (a,p)<-mons]
        convExp p           = Vec (zeroes++(p:tailZeroes))
        (zeroes,tailZeroes) = (map (const 0) vs, map (const 0) vs')

instance (Convertible a b,AddGroup b)=> Convertible (Pol a) (UPol b)
  where  cvm (Pol mons a _ vars _) (UPol _ b v dom') =
    -- multivariate  f  is convertible to  univariate  g  iff 
    --   polCoef(f)  is convertible to  upolCoef(g)   and
    --   v = pHeadVar f  belongs to  vars = pVars g   and
    --   f  depends only on  v  (deg(x,f)=0 for x/=v).
    -- In this case, to convert f to g  means to 
    -- convert coefficient in each monomial removing the obtained 
    --   zero monomials, 
    -- convert each power product by extracting the only nonzero
    --   component (or 0 for zero pp).
    case  (zeroS b, cvm a b, span (/=v) vars)
    of( _, Nothing, _       ) -> Nothing
      ( _, _      , (_ ,[]) ) -> Nothing
      ( z, _      , (vs,_ ) ) -> 
        let        n     = genLength vs
          mons' = filter ((/= z) . fst)
                                [(cv a b,vecRepr p) | (a,p) <- mons]
          convMon (c,js) = case  genericSplitAt n js  of 
            (ks,j:ls) -> if  all (==0) ks  &&  all (==0) ls  then  
                                                          Just (c,j)
                         else  Nothing
        in  (case  allMaybes (map convMon mons')  of
                                  Just ms -> Just (UPol ms b v dom')
                                  _       -> Nothing)

instance (Convertible a b,AddGroup b) => Convertible (Pol a) (Pol b)
  where cvm (Pol mons a _ vars _) (Pol _ b ord' vars' dom') =
    -- f  is convertible to  g  iff 
    -- * polCoef(f) is convertible to polCoef(g)  and
    -- * pVars f    is a subset of  pVars g.
    -- In this case the conversion means converting coefficients,
    -- extending the pp-s with zeroes and permutating them to match
    -- the new variable list, removing zero coefficient (converted) 
    -- monomials and re-ordering their list under ord'.
    case  (zeroS b, cvm a b, all (`elem` vars') vars) of
      (_, Nothing, _    ) -> Nothing       (_, _      , False) -> Nothing
      (z, _      , _    ) -> 
        let  pm = permut (vars++(vars'\\vars)) vars'
            --           [v1..vn]
            -- For this [v1..vn],  pm = [i1..in],
            -- where i(k) is the position of v(k) in  vars'.
            -- So, it remains to apply pm to the pp-s of  mons.
          permut xs ys = case  zip ys ([1..] ::[Z])
                         of ps -> [lookup x ps| p <- xs]
          monsC = filter ((/=z).fst) [(cv a b,convPP p)| (a,p)<- mons]
       convPP (Vec js) = Vec$ map snd$ sortBy (compBy fst) (zip pm js)
        in  Just (reordPol ord' (Pol monsC b ord' vars' dom'))


   do we need this  ?

   -- For a base set  sR  of the base ring  rR  build the embedded 
   -- subset  sR'  in (Pol rR)
baseSetToPolSubset :: 
          (Ring a) => PPComp -> [PolVar] -> OSet a -> OSet (Pol a)
                                                      -- sSP
baseSetToPolSubset    cp        vars        sS =
  let  bounds'  = ([],[],[],[]);   constrs' = [];   opers'   = []
    c = case  osetPointed sS  of     [[c']] -> c'
          _      -> error.. "chosenElement sS  must yield [[c]] "..
    elem' = cToPol c cp vars
    list' = case  osetList sS  of []   -> []
                                  [xs] -> [cToPol x cp vars | x<-xs]
    props' = [(IsBaseSet,      No ), (FullType,     No ),                 
              (OrderIsTrivial, Yes), (OrderIsTotal, No ), --so far
              (OrderIsNoether, Yes), (OrderIsArtin, Yes), --so far
              (Finite, isFiniteSet sS)]               
    bel        =  membership sS
    belongs' f =  isZero f  ||  (isZero (lpp f) && bel (lc f))
  in OSet  elem'   belongs'  (card sS)  [[elem']]  list'  bounds' 
        props'  constrs'  opers'
------------------------------------------------------------------
baseSemigroupToPolSubsemigroup ::   (Ring a) => 
      PPComp -> [PolVar] -> Subsemigroup a -> Subsemigroup (Pol a)
baseSemigroupToPolSubsemigroup  cp vars sSG =
  let     sS'     = baseSetToPolSubset cp vars (subsmgSet sSG)
    smgType = subsmgType sSG;  props   = subsmgProps sSG
    zero_un' = case  subsmgUnity sSG  of  [[]]   -> [[]]
                                   []     -> []
                                   [[zu]] -> [[cToPol zu cp vars]]
    gens' = case  subsmgGens sSG  of []     -> []
                          [gens] -> [[cToPol x cp vars]| x<-gens]
    [Just comm,Just gr,Just cyc] = [lookup p props | p <-
                           [Commutative,IsGroup,IsCyclicSemigroup] ]
    props' =  [(Commutative          , comm   ), 
               (IsGroup              , gr     ),  
               (IsMaxSubsemigroup    , No     ), 
               (IsCyclicSemigroup    , cyc    ),  
               (IsOrderedSubsemigroup, Unknown)]   --so far
    constrs' =  []   -- so far;  opers'   =  []   -- so far
  in   Subsemigroup smgType sS' zero_un' gens' props' constrs' opers'
--------------------------------------------------------------------
***  finish this and then  FinGenExt  in  Ring (Pol a)
baseRingToPolSubring :: 
    (Ring a) => PPComp -> [PolVar] -> Subring a -> Subring (Pol a)
                -- cp     vars        rR           rP
baseRingToPolSubring  cp vars rR = 
  let ...
  in  Subring  addSubgroup'' mulSemigroup'' char' gens'' props''
             constrs'' opers''                     
    (Subring  addSubgroup' mulSubsemigroup' char' gens' props' 
              constrs' opers'                              ) =  rR'
    gens'' = [cToPol c cp vars | c <- gens']
    props'' =
      [(IsField      ,  - R'  ), (HasZeroDiv    , - R'  ),
       (HasNilp      ,  - R'  ), (IsPrimaryRing , - R ' ),
       (Euclidean    ,  - R'  ), (Factorial     , - R'  ),  
       (PIR           , - R'  ), (FactorialT** , factT' ), 
       (IsRealField   , - R'  ), (IsOrderedRing,  - R'  ), 
       (MinDivRem**  , euc'   ), (IsGxRing      , gb'   ), 
       (SyzygySolve**, gb'    ), (ModBasCan**   , gb'   )
      ]
********************************************************************
-}
