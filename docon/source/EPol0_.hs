------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------




module EPol0_   -- Extended Polynomial. Several useful items.
                -- EPol  is used sometimes as the representation for
                --                                Vector of Polynomials.
                -- All needed from here is reexported by  Pol.

(EPP, EPPComp, EPPOTerm, EMon, EPol(..),
 eppoECp, eppoMode, eppoWeights, eppoCp, epolMons, epolPol, 
 epolEPPOTerm, epolECp, epolPPCp, eLm, eLpp, epolLCoord, reordEPol, 
 leastEMon, cToEMon, cToEPol, zeroEPol, polToEPol, epolToPol, 
 ecpTOP_weights, ecpPOT_weights, ecpTOP0  
 -- , instances for EPol: 
 --  Length(..) Dom Cast PolLike Show DShow Eq Set .. AddGroup Num
)
where
import qualified Data.Map as Map (lookup, insert)

import Data.List hiding (maximum, sortBy)
import Prelude   hiding (maximum)

import DPrelude   
       (Length(..), DShow(..), Cast(..), -- classes
        Natural, InfUnn(..), PropValue(..), Comparison,
        ct, ctr, allMaybes, antiComp, sortBy, isOrderedBy, maximum, 
        tuple41, tuple42, tuple43, tuple44, showsn, showsWithDom
       )
import Categs
import SetGroup (Set(..), AddSemigroup(..), MulSemigroup(..), 
                 AddMonoid(), AddGroup(..),  compareTrivially, zeroS, 
                                                isZero, neg, sub, times)
import RingModule (Ring(..), CommutativeRing())
import DPair      () 
import VecMatr    (vecSize)
import UPol_      (PolLike(..))
import Pol_       (Pol(..), polMons, polPPComp )
import Pol1_      ()






------------------------------------------------------------------------
type EPP = (Natural, PowerProduct)    
                                -- in the Extended power product (i, pp)
                                -- i = 1, 2, ...  is the coordinate No
type EPPComp = Comparison EPP

------------------------------------------------------------------------
ecpTOP_weights, ecpPOT_weights ::
                             Bool -> [PowerProduct] -> PPComp -> EPPComp
                          -- mode    weights           cp

  -- are the widely used EPP-comparisons induced by the  
  -- pp-comparison  cp  and a list of weights  w(1), w(2), ...
  -- w(i) :: PowerProduct  is for the coordinate No i.
  --
  -- TOP stands for the "term over position",  POT - the inverse.
  -- TOP means compare first the  pp  parts of  (i,p), (j,q)  by  
  -- cp (w(i)+p) (w(j)+q),  then, if equal, compare the positions.
  --
  -- They say, this TOP,POT terminology is by 
  --                                         W.Adams & P.Loustaunau.
  -- mode  describes the comparison for the positions (integers).
  --       mode = True   means  `compare'     - the straight order,
  --              False         flip compare  -     reverse  order.
  --
  -- Example:  ecpTOP_weights False [w1,w2,w3] degLex (3,p) (1,q)
  --           means  case  degLex (w3+p) (w1+q)  of  EQ -> LT
  --                                                  v  -> v

ecpTOP_weights mode weights cp (i, p) (j, q) =
  case  
      (genericDrop (pred i) weights, genericDrop (pred j) weights)
  of 
  (wi: _, wj: _) -> case (cp (wi + p) (wj + q), compare i j)
                    of
                    (EQ, v) -> if mode then v else antiComp v
                    (v,  _) -> v
  _           -> 
      error $ msgEcpTPLeng "ecpTOP_weights" (head weights) (i, p) (j, q)

msgEcpTPLeng str w ip jq = 
                   concat [str, " mode weights cp (i, p) (j, q),\nhead \
                                                           \weights = ",
                           shows w "\n(i, p)       = ", shows ip 
                           "\n(j, q)       = ",  shows jq
                           "\n\ni or j  >  length(weights).\n"]

-- positions compared first:

ecpPOT_weights mode weights cp (i, p) (j, q) =  
  case 
      compare i j 
  of
  EQ -> 
       case (genericDrop (pred i) weights, genericDrop (pred j) weights)
       of 
       (wi: _, wj: _) -> cp (wi + p) (wj + q) 
       _              -> 
              error $
              msgEcpTPLeng "ecpPOT_weights" (head weights) (i, p) (j, q)
      
  v  -> if mode then  v  else  antiComp v


ecpTOP0 :: Bool -> PPComp -> EPPComp

-- Specialization of ecpTOP_weights to zero weights.
-- Compares first pp by cp, then, if equal, sees the position No.

ecpTOP0 mode cp (i, p) (j, q) = 
                            case (cp p q, compare i j)  
                            of
                            (EQ, v) -> if mode then  v  else  antiComp v
                            (v,  _) -> v

------------------------------------------------------------------------
type EPPOTerm = (EPPComp, String, [PowerProduct], PPComp)
                 -- ecp   mode    wts             cp

eppoECp     :: EPPOTerm -> EPPComp 
eppoMode    :: EPPOTerm -> String
eppoWeights :: EPPOTerm -> [PowerProduct]
eppoCp      :: EPPOTerm -> PPComp

eppoECp     = tuple41
eppoMode    = tuple42
eppoWeights = tuple43
eppoCp      = tuple44


-- eterm = (ecp, mode, wts, cp)   describes the epp ordering. 
--
-- ecp          an epp comparison function, is the main part.
-- mode = 'a':_
--   means that ecp agrees with the pp-ordering cp' contained in the
--   polynomial sample of e-polynomial:
--   cp'  and  (ecp restricted to any fixed i)  define the same 
--   ordering.
--
-- wts is a list of weights, each related to its position in vector.
-- wts = []  means the weights and  cp  are ignored.
-- Otherwise, it means that  ecp  is defined as the TOP or POT
-- comparison respectively to  wts  and  cp.
-- 
-- mode  = [aMode, tMode, dMode]
-- aMode = 'a'   means ecp agreed with pp-ordering from the
--               polynomial sample in e-polynomial.
-- tMode = 't'            means TOP comparison
--         other letter   ...   POT comparison.
-- dMode = 'l'            means the less position No is considered
--                        as greater,
--         other letter   means the inverse direction.
--
-- Examples.
-- (ecp, "", [], _, _)  means no extra description for ecp is given.
--
-- (ecp, "atl", [w1,w2], degLex)
--   means the agreed TOP-degLex-reverse comparison
--                               ecpTOP_weights False [w1,w2] degLex 

------------------------------------------------------------------------
type EMon a = (a, EPP)
data EPol a = EPol [EMon a] EPPOTerm (Pol a)

-- EPol  is the  indexed monomial-wise respesentation  for 
--       polynomial vector. Widely used in Groebner bases for the
--       vectors over polynomials.
-- In  EPol emons eterm pol
-- pol     is the sample polynomial; it is often set zero.
-- eterm = (ecp,_,_,_)
-- ecp     is an admissible extended power product comparison.
-- See the example of  EPol  in  Manual.

------------------------------------------------------------------------
instance Length (EPol a) where  genLength = genLength . epolMons 

instance Eq a => Eq (EPol a) where f == g =  (epolMons f == epolMons g)

epolMons     :: EPol a -> [EMon a]
epolEPPOTerm :: EPol a -> EPPOTerm
epolPol      :: EPol a -> Pol a
epolECp      :: EPol a -> EPPComp

epolMons     (EPol ms _ _) = ms
epolEPPOTerm (EPol _  t _) = t
epolPol      (EPol _  _ p) = p 
epolECp = eppoECp . epolEPPOTerm

epolPPCp = polPPComp . epolPol 
                               -- the one contained in polynomial sample

eLm :: CommutativeRing a => EPol a -> EMon a    -- leading e-monomial
eLm f = case epolMons f  
        of  
        m :_ -> m
        _    -> error ("\neLm 0 in  " ++ (showsDomOf 1 f ".\n"))

eLpp :: CommutativeRing a => EPol a -> EPP
eLpp = snd . eLm

epolLCoord :: CommutativeRing a => EPol a -> Natural
epolLCoord = fst . eLpp                -- coordinate of leading monomial

leastEMon :: CommutativeRing a => EPol a -> EMon a  
leastEMon f =  
        case epolMons f  
        of          
        m: ms -> last (m: ms)
        _     -> error ("\nleastEMon 0  in  " ++ (showsDomOf 1 f ".\n"))

zeroEPol :: EPPOTerm -> Pol a -> EPol a
zeroEPol    t           f     =  EPol [] t f

------------------------------------------------------------------------
instance Dom EPol where  dom    = dom    . epolPol
                         sample = sample . epolPol

instance AddGroup a => Cast (EPol a) (EMon a) 
  where
  cast mode (EPol _ t p) (a, e) =  EPol mons t p
            where
            mons =  if mode == 'r' && isZero a  then []  else [(a, e)]


instance AddGroup a => Cast (EPol a) [EMon a] 
  where
  cast mode (EPol _ cp p) mons =  EPol ms cp p    -- order NOT checked
       where
       z  = zeroS $ sample p
       ms = if mode /= 'r' then  mons  else  filter ((/= z) . fst) mons


------------------------------------------------------------------------
instance PolLike EPol
  where
  varPs _ f = error ("\nvarPs c f   is senseless for  EPol.\n" ++
                                           (showsWithDom 1 f "f" "" "")) 
  pFreeCoef f = error ("\npFreeCoef f  is senseless for EPol.\n" ++
                                           (showsWithDom 1 f "f" "" ""))
  pFromVec f _ = error ("\npFromVec f coefs   is senseless for EPol.\n"
                                        ++ (showsWithDom 1 f "f" "" ""))
  pToVec n f = error $ concat 
                   ["\npToVec ", shows n " f  is senseless for EPol.\n",
                                           showsWithDom 1f "f" "" ".\n"]
  pIsConst = all (isZero . snd . snd) . epolMons
  pVars    = pVars   . epolPol
  pCoefs   = map fst . epolMons 

  pCoef f []      = error 
                    ("\npCoef f []\n" ++ (showsWithDom 1 f "f" "" "."))
  pCoef f (j: js) = 
          let {p = (j, Vec js);  cp = epolECp f;  z = zeroS $ sample f}
          in
          case  dropWhile ((== LT) . cp p . snd) $ epolMons f
          of
          (a, q): _ -> if p == q then  a  else  z
          _         -> z

  lpp  = snd . eLpp          -- :: PowerProduct, in addition to eLpp
  pPPO = pPPO . epolPol      -- :: PPComp
  ldeg = sum . vecRepr . lpp 

  deg f = case  map (sum . vecRepr . snd . snd) $ epolMons f 
          of
          d: ds -> maximum (d:ds)         
          _     -> error ("\ndeg 0  for  " ++ (showsDomOf 1 f ".\n"))
         
  pTail f = case epolMons f 
            of 
            _: ms -> ct f ms
            _     -> error ("\npTail 0  in  " ++ (showsDomOf 1 f ".\n"))

  lm f = if  null $ epolMons f  then
                         error ("\nlm 0  in  " ++ (showsDomOf 1 f "\n"))
         else           
         (c, p)  where  (c, (_, p)) = eLm f
                                         -- :: Mon a, in addition to eLm

  degInVar for0 i f =  -- maximum
                       -- deg_i mon | mon<- unExtendedMonomialsOf_f]
                       --
           degInVar for0 i $ Pol ms c o vs d
                   where
                   ms             = [(a, p) | (a, (_, p)) <- epolMons f]
                   Pol _ c o vs d = epolPol f

  pMapCoef mode f g = cast mode g [(f a, e) | (a, e) <- epolMons g]

  pMapPP f g =  ct g [(a, (j, Vec ks)) | (a, (i, Vec js)) <- epolMons g,
                                                 let  j: ks = f (i: js)]
  pCDiv f c = let (cs, eps) = unzip $ epolMons f
              in
              case allMaybes [divide_m a c | a <- cs]
              of
              Just qs -> Just $ ct f $ zip qs eps
              _       -> Nothing

  pDeriv  mInd  f@(EPol emons _ g) =  ctr f $ map monDeriv emons
                                   -- differentiate each e-monomial ...
    where
    monDeriv (b, (i, p)) = case polMons $ pDeriv mInd $ ct g (b, p) 
                           of
                           [(c, q)] -> (c, (i, q))        
                           []       -> (z, (i, p))
    z = zeroS $ sample g

  pValue f _ = error ("\npValue f coefs   for EPol:  to be defined in \
                      \future.\n" ++ (showsWithDom 1 f "f" "" "."))
  pDivRem f _ = error ("\npDivRem f g  for EPol:  to be defined in \
                       \future.\n" ++ (showsWithDom 1 f "f" "" "."))

------------------------------------------------------------------------
reordEPol :: EPPOTerm -> EPol a -> EPol a -- bring to given epp ordering
reordEPol t (EPol ms _ pol) = 
                     let {ecp = eppoECp t;  cmp (_, p) (_, q) = ecp q p}
                     in  EPol (sortBy cmp ms) t pol 

cToEMon :: [a] -> Natural -> b -> EMon b
cToEMon    xs     i          b = (b, (i, Vec $ map (const 0) xs))

cToEPol :: AddGroup a => EPol a -> Natural -> a -> EPol a
                         -- sample
cToEPol (EPol _ t f) i a =
  if
     a == zeroS a  then  EPol []                      t f
  else                   EPol [cToEMon (pVars f) i a] t f


------------------------------------------------------------------------
polToEPol :: Natural -> EPPOTerm -> Pol a -> EPol a

-- embed polynomial to the e-polynomial of the given constant 
-- coordinate No i and epp ordering term

polToEPol i o f = EPol [(c, (i, p)) | (c, p) <- polMons f] o f
                       
                 -- the inverse operation is correct 
                 -- ** if the polynomial power products do not repeat **
                 --
epolToPol :: AddGroup a => EPol a -> Pol a
epolToPol (EPol ms _ f) = ct f [(a, p)| (a, (_, p)) <- ms]


epolneg_ :: AddGroup a => EPol a -> EPol a
epolneg_ f =  ct f [(neg a, p)| (a, p) <- epolMons f]

{-# specialize epolneg_ :: EPol Integer -> EPol Integer #-}

------------------------------------------------------------------------
epoladd_ :: AddGroup a => EPol a -> EPol a -> EPol a
epoladd_                  (EPol ms o pol) g = 
  case 
      (zeroS $ sample pol, eppoECp o) 
  of
  (z, cp) -> ct g $ epa ms $ epolMons g
    where
    epa []       msG      = msG
    epa msF      []       = msF
    epa (m: msf) (n: msg) =
        let {(a, p) = m;  (b, q) = n;  c = add a b}
        in  
        case cp p q  
        of
        GT -> m: (epa msf (n: msg))  
        LT -> n: (epa (m: msf) msg)
        _  -> if c == z then  epa msf msg  else  (c, p): (epa msf msg)


epoltm :: Ring a => (a -> j -> a) -> EPol a -> j -> EPol a 
epoltm              t                f         n =  
                               ctr f [(t a n, e) | (a, e) <- epolMons f]
  -- t = `times' on `a'

------------------------------------------------------------------------
instance CommutativeRing a => Show  (EPol a) where 
                                             showsPrec _ = showsn 0
instance CommutativeRing a => DShow (EPol a)   
  where
  dShows opt (EPol ms _ f) =
          let indexedPols = [(i, ct f (a, p)) | (a, (i, p)) <- ms]  
          in
          showString "(EPol " . dShows opt indexedPols . showString " )"

------------------------------------------------------------------------
instance CommutativeRing a => Set (EPol a)   
  where
  compare_m         = compareTrivially
  showsDomOf verb f = showString "{EPol " . shows (pVars f) . 
                      showChar ' ' . showsDomOf (pred verb) (sample f) . 
                      showChar '}'

  fromExpr (EPol _ o pol) e =  
    let
      (sampleIndexedPol, cp) = ((1, pol), eppoECp o)
      cmp (_, p) (_, q)      = cp q p
    in 
    (case fromExpr [sampleIndexedPol] e
     of
     ([iPols], "" ) -> case sortBy cmp $ map toEMon iPols
                       of
                       ms -> ([EPol ms o pol], "")
     (_,       msg) -> ([], msg)
    )
    where 
    toEMon (i, f) = 
          case polMons f
          of
          [(a, p)] -> (a, (i, p))
          _        -> error $ concat 
                      ["\nfromExpr  f@(EPol..)  expr,\nPol domain is  ",
                       showsDomOf 1 pol "\nexpr =  ",  showsn 1 e 
                       "\n\nexpr  must parse to the list of \
                       \(i,f_i),\nf_i  a monomial polynomial.\n"]
  ----------------------------------------------------------------------
  baseSet  f@(EPol _ o (Pol _ c _ vars aD))  dom =
     case
         (Map.lookup Set dom, zeroS c, o, Map.lookup Set aD)
     of
     (Just (D1Set s), _,  _                ,_               ) -> 
                                                                (dom, s)
     (_,              zr, (ecp, md, wts, _), Just (D1Set aS)) ->
       let                    
         bel' mode (EPol emons' o' p') =  
           let
             (ecp', md', wts', _) = o'
             bel                  = membership aS

             bl = if mode == 'r' then  all (bel 'r')  
                  else                 const True

             (l, vars', (coefs, eps)) =
                                (genLength vars, pVars p', unzip emons')
           in
           vars == vars'  &&  all (/= zr) coefs
           &&  all (== l) (map (vecSize . snd) eps)
           &&  isOrderedBy (flip ecp ) eps 
           &&  isOrderedBy (flip ecp') eps
           &&  md == md'  &&  wts == wts'  &&  bl coefs 

         props' = [(Finite,         No ), (IsBaseSet,    Yes),
                   (FullType,       No ),  
                   (OrderIsTrivial, Yes), (OrderIsTotal, No ),
                   (OrderIsNoether, Yes), (OrderIsArtin, Yes)
                  ]
         s = OSet 
             {osetSample  = f,          membership  = bel',
              osetCard    = Infinity,   osetPointed = Just $ Just f,
              osetList    = Nothing,
              osetBounds  = (Nothing, Nothing, Nothing, Nothing),
              osetProps   = props', 
              osetConstrs = [],       
              osetOpers   = []}
       in
       (Map.insert Set (D1Set s) dom, s)


------------------------------------------------------------------------
instance CommutativeRing a => AddSemigroup (EPol a)   
  where
  add                 = epoladd_
  zero_m (EPol _ o f) = Just $ zeroEPol o f
  neg_m               = Just . epolneg_ 
  times_m f           = Just . epoltm times f

  baseAddSemigroup (EPol _ o pol) dom =
    case  
        Map.lookup AddSemigroup dom  
    of
    Just (D1Smg s) -> (dom, s)
    _              ->
      let
        zeroE  = zeroEPol o pol
        props' = [(Commutative,           Yes    ), 
                  (IsGroup,               Yes    ),  
                  (IsMaxSubsemigroup,     No     ), 
                  (IsCyclicSemigroup,     No     ),  
                  (IsOrderedSubsemigroup, Unknown)]
        s = 
          Subsemigroup
          {subsmgType    = Add,     subsmgUnity = Just $ Just zeroE,
           subsmgGens    = Nothing, subsmgProps = props',
           subsmgConstrs = [],      subsmgOpers = []}
      in
      (Map.insert AddSemigroup (D1Smg s) dom, s)


------------------------------------------------------------------------
instance CommutativeRing a => AddMonoid (EPol a)
instance CommutativeRing a => AddGroup  (EPol a)
  where
  baseAddGroup (EPol _ o pol) dom = 
    case 
        Map.lookup AddGroup dom  
    of
    Just (D1Group g) -> (dom, g)
    _                ->
      let
        zeroE  = zeroEPol o pol
        props' = [(IsCyclicGroup,    No ),   (IsNormalSubgroup, Yes), 
                 (IsMaxSubgroup,     No ),   (IsPrimeGroup,     No ),
                 (IsOrderedSubgroup, Unknown)]
        g = Subgroup 
            {subgrType    = Add,                subgrGens  = Nothing,
             subgrCanonic = Just $ const zeroE, subgrProps = props',
             subgrConstrs = [],                 subgrOpers = []}
      in
      (Map.insert AddGroup (D1Group g) dom, g)


------------------------------------------------------------------------
instance CommutativeRing a => Num (EPol a)  
  where 
  negate = neg
  (+)    = add
  (-)    = sub  
  _ * _  = 
          error "\n(EPol ..)*(EPol _):  product is not defined there.\n"
  signum _ = error "\nsignum (EPol _):  it is senseless there.\n"
  abs    _ = error "\nabs (EPol _):  it is senseless there.\n"
  fromInteger _ =
          error "\nfromInteger _  to (EPol _):   use  fromi  instead.\n"
