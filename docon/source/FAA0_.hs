------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------




module FAA0_  -- Free Associative Algebra  (non-commutative polynomials)
              --                                over a Commutative Ring.
(module FreeMonoid,

 FAA(..), FAAMon, FAAVarDescr,
 faaMons, faaFreeMOrd, faaVarDescr, faaN, faaVMaps, faaFreeMOId,
 faaFreeMOComp, faaLM, faaLeastMon, faaLPP, reordFAA, faaMonMul, 
 faaMonFAAMul, cToFAA, faaToHomogForms
 -- instances for FAA :
 --   Dom, Eq, Show, DShow, Cast (FAA a) (FAAMon a), 
 --                         Cast (FAA a) [FAAMon a], Cast (FAA a) a,
 --   PolLike FAA, Set .. Ring, Fractional
)
where
import qualified Data.Map as Map (lookup)

import Data.Maybe (catMaybes) 

import DPrelude (DShow(..), Cast(..), -- classes
                 Z, PropValue(..), Expression(..), 
                 ct, ctr, Comparison, sortBy, allMaybes, partitionN,
                 less_m, showsn, addToShowOptions)
import Categs
import SetGroup
import RingModule
import UPol_      (PolLike(..), PPOId, PolVar, lc)
import FreeMonoid




------------------------------------------------------------------------
type FAAMon a = (a, FreeMonoid) 

type FAAVarDescr = (Maybe Z, (Z -> Maybe PolVar, PolVar -> Maybe Z))
                    -- mn     toStr              fromStr     
-- mn       is as in FreeMonoid.
-- variable indices range in   iRange = [1 .. upp],  
-- upp = n  (case mn = Just n)  or  infinity  (case mn = Nothing).
-- toStr    shows variable as string, it is defined on iRange  and 
--          produces  Just str  for some (showable) indices.  
-- fromStr  is the reverse to  toStr,  it produces  Just index  for a
--          variable name which corresponds to some index in  iRange. 

data FAA a =  FAA [FAAMon a] a FreeMOrdTerm FAAVarDescr (Domains1 a)
--
-- (element of) a Free associative algebra 
-- - Non-commutative polynomial.


instance Dom FAA where  dom    (FAA _ _ _ _ d) = d
                        sample (FAA _ c _ _ _) = c

faaMons       :: FAA a -> [FAAMon a]
faaFreeMOrd   :: FAA a -> FreeMOrdTerm
faaVarDescr   :: FAA a -> FAAVarDescr
faaN          :: FAA a -> Maybe Z
faaVMaps      :: FAA a -> (Z -> Maybe PolVar, PolVar -> Maybe Z)
faaFreeMOId   :: FAA a -> PPOId
faaFreeMOComp :: FAA a -> Comparison FreeMonoid

faaMons     (FAA ms _ _ _  _) = ms
faaFreeMOrd (FAA _  _ o _  _) = o
faaVarDescr (FAA _  _ _ vd _) = vd
faaN                          = fst . faaVarDescr 
faaVMaps                      = snd . faaVarDescr 

faaFreeMOId   = freeMOId   . faaFreeMOrd
faaFreeMOComp = freeMOComp . faaFreeMOrd

faaLM, faaLeastMon :: Set a => FAA a -> FAAMon a

faaLM f = case faaMons f 
          of
          m: _ -> m
          _    -> error ("\nfaaLM 0  in  FAA R,\nR = " ++ 
                                         (showsDomOf 1 (sample f) "\n"))
faaLeastMon f = case faaMons f 
                of
                m: ms -> last (m: ms)
                _     -> error ("\nfaaLeastMon 0  in  FAA R,\nR = " ++
                                        (showsDomOf 1 (sample f) ".\n"))

faaLPP :: Set a => FAA a -> FreeMonoid
faaLPP f = case faaMons f 
           of
           (_, p): _ -> p
           _         -> error ("\nfaaLPP 0  in  FAA R,\nR = "
                               ++ (showsDomOf 1 (sample f) ".\n"))

instance Eq a => Eq (FAA a) where  f == g =  (faaMons f) == (faaMons g)

reordFAA :: FreeMOrdTerm -> FAA a -> FAA a    -- bring to given ordering
reordFAA o (FAA ms c _ vd dom) = FAA (sortBy cmp ms) c o vd dom
                                     where
                                     cmp (_, p) (_, q) = cp q p
                                     cp                = freeMOComp o

------------------------------------------------------------------------
instance AddGroup a => Cast (FAA a) (FAAMon a)
  where
  cast mode (FAA _ c o vd d) (a, p) =  FAA mons c o vd d
            where
            mons = if  mode == 'r' && isZero a  then []  else [(a, p)]

instance AddGroup a => Cast (FAA a) [FAAMon a]
  where
  cast mode (FAA _ c o vd d) mons =  FAA ms c o vd d
    where                                          -- order NOT checked
    z  = zeroS c
    ms = if  mode /= 'r'  then  mons  else  filter ((/= z) . fst) mons

instance AddGroup a => Cast (FAA a) [(a, [(Z, Z)])]
  where
  cast mode f preMons = 
               cast mode f [(a, FreeM (faaN f) ps) | (a, ps) <- preMons]

instance Ring a => Cast (FAA a) a
  where
  cast mode (FAA _ _ o vd d) a =  
                   case (mode, isZero a) 
                   of
                   ('r', True) -> FAA []                       a o vd d
                   _           -> FAA [(a, FreeM (fst vd) [])] a o vd d

------------------------------------------------------------------------
instance PolLike FAA
  where
  pPPO     _   = error "\npPPO (FAA _):   use  faaNCPPO  instead.\n"
  lm       _   = error "\nlm (FAA _):   use  faaLM  instead.\n"
  lpp      _   = error "\nlpp (FAA _):  use  faaLPP  instead.\n"
  pCoef    _ _ = error "\npCoef  is not defined for  FAA R.\n"
  pFromVec _ _ = error "\npFromVec  is not defined for  FAA R.\n"
  pToVec   _ _ = error "\npToVec  is not defined for  FAA R.\n"
  pDeriv   _   = error ("\npDeriv (FAA _):   derivative skipped, so "
                        ++"far, for non-commutative polynomial.\n"
                       )
  pMapPP  _ _ = error "\npMapPP f (FAA _):  not defined.\n"
  pDivRem _ _ = error "\npDivRem  is not defined so far for  FAA R.\n"
  pValue  _ _ = error "\npValue   is not defined so far for  FAA R.\n"

  pIsConst f = case faaMons f of (_, p): _ -> p == unity p
                                 _         -> True

  pVars f = catMaybes $ map toStr js  
                      where 
                      (mn, (toStr, _)) = faaVarDescr f
                      js               = case mn of Just n -> [1 .. n]
                                                    _      -> [1 ..  ]
  pCoefs  = map fst . faaMons
  pTail f = case faaMons f 
            of
            _: ms -> ct f ms
            _     -> error ("\npTail 0  in  FAA R,\nR = " ++
                                        (showsDomOf 1 (sample f) ".\n"))
  pFreeCoef (FAA mons c _ _ _) =
              let {z = zeroS c;  (a, p) = last mons}
              in
              if null mons then  z  else  if p == unity p  then a else z

  ldeg f = case faaMons f
           of
           (_, p): _ -> sum $ map snd $ freeMRepr p
           _         -> error ("\nldeg 0  in  FAA R,\nR = " ++
                                        (showsDomOf 1 (sample f) ".\n"))

  deg f = case  map (sum . map snd . freeMRepr . snd) $ faaMons f
          of
          d: ds -> maximum (d: ds)
          _     -> error ("\ndeg 0  in  FAA R,\nR = " ++
                                        (showsDomOf 1 (sample f) ".\n"))

  degInVar for0 i f =
    -- Put degree of i-th variable in monomial to be the sum of
    -- degrees of its occurences. 
    -- Example:   if    faaMons f = [(1,1),(2,2),(5,3),(2,6)]  then
    --                                              degInVar _ 2 f = 8.
    (case (i >= 0, faaMons f)
     of
     (False, _ ) -> error $ msg "\n\nPositive i needed.\n"
     (_,     []) -> for0
     (_,     ms) -> maximum $ map (degInMon i . freeMRepr . snd) ms
    )
    where
    degInMon i = sum . map snd . filter ((== i) . fst)

    msg = showString "\ndegInVar for0 i f,\ni = " . shows i .
          showString "\nf <- FAA R,  R = " . showsDomOf 1 (sample f) 

  pCDiv f c = let (cs, pps) = unzip $ faaMons f
              in
              case allMaybes [divide_m a c | a <- cs]
              of
              Just quots -> Just $ ct f $ zip quots pps
              _          -> Nothing

  pMapCoef mode f g = cast mode g [(f a, pp) | (a, pp) <- faaMons g]

  varPs a f = [ctr f [(a, FreeM mn [(i, 1)])] | i <- range]
                                where
                                mn    = faaN f
                                range = case mn of Just n -> [1 .. n]
                                                   _      -> [1 ..  ]

------------------------------------------------------------------------
neg_ :: AddGroup a => FAA a -> FAA a                          -- f -> -f
neg_ f =  ct f [(neg a, pp) | (a, pp) <- faaMons f]
 
add_ :: AddGroup a => FAA a -> FAA a -> FAA a
add_ (FAA monsF c o _ _) g =  ct g $ pa monsF $ faaMons g
  where
  (z, cp) = (zeroS c, freeMOComp o)

  pa []       msG     = msG
  pa msF      []      = msF
  pa (m: msf) (n: msg) =
            let {(a, p) = m;  (b, q) = n;  d = add a b}
            in
            case cp p q
            of
            GT -> m: (pa msf (n: msg))
            LT -> n: (pa (m: msf) msg)
            _  -> if d == z then  pa msf msg  else  (d, p): (pa msf msg)

------------------------------------------------------------------------
faaMonMul :: Ring a =>  a -> FAAMon a -> FAAMon a -> [FAAMon a]
                     -- zero
faaMonMul z (a, p) (b, q) =  let c = a*b in  if c == z  then  []
                                             else         [(c, mul p q)]

faaMonFAAMul :: Ring a => FAAMon a -> FAA a -> (FAA a, FAA a)
 
-- multiply FAA element f by FAA monomial m forming the pair (m*f, f*m)
  
faaMonFAAMul (a, p) f = (ctr f [(a*b, mul p q) | (b, q) <- faaMons f],
                         ctr f [(b*a, mul q p) | (b, q) <- faaMons f])

times_ :: Ring a => (a -> i -> a) -> FAA a -> i -> FAA a
times_              t                f        n =
                                ctr f [(t a n, p) | (a, p) <- faaMons f]
  -- t = `times' for `a'
                                 
cToFAA :: Ring a =>                                -- coefficient to FAA
          FreeMOrdTerm -> FAAVarDescr -> Domains1 a -> a -> FAA a
cToFAA    ord             varDescr       dom           a =
                                             FAA mons a ord varDescr dom
          where 
          mons = if isZero a then [] else [(a, FreeM (fst varDescr) [])]
                       

faaToHomogForms ::
             (AddGroup a, Eq b) => (FreeMonoid -> b) -> FAA a -> [FAA a]
                                   -- weight map
faaToHomogForms w f =
     map (ct f) $ partitionN (\ (_, p) (_, q) -> w p == w q) $ faaMons f
     --
     -- (non-ordered) list of homogeneous forms of non-commutative 
     -- polynomial over `a'  with respect to  weight:: PowerProduct -> b


instance Ring a => Show  (FAA a) where showsPrec _ = showsn 0 
instance Ring a => DShow (FAA a) 
  where 
  dShows opt (FAA mons c _ varDescr dom) = 

  -- If  a  is and Ordered ring, then the mode `ord'  is set which
  -- writes ..- m  instead of ..+(-m) for the negative coefficient
  -- monomials.
  -- If  a  has unity  then unity coefficient images  are skipped.

   (case (zeroS c, unity_m c, Map.lookup Ring dom)
    of
    (zr, unM, Just (D1Ring rR)) -> ss zr unM $ isOrderedRing rR
    _                           ->
               error $ msg 
               "\n\nthe Ring term is not found in coefficient domain.\n"
   )
   where
   msg = showString "\ndShows f str,\nf <- FAA R,  R = " . 
         showsDomOf 1 c . showString ",\nPower products = " . 
         showsn 1 (map (freeMRepr . snd) mons)
   msg' = showString "\n\nWrong representation for  f:\n"
   opt' = addToShowOptions (-1) opt

   ss zr unM ordered =  showChar '(' . wr mons' . showChar ')'
     where
     mons'   = [(c, freeMRepr v) | (c, v) <- mons]
     wr mons = 
       case (ordered, mons) 
       of
       (_,   []           ) -> showChar '0'
       (_,   [m]          ) -> wMon m
       (Yes, m: (c, p): ms) ->
          if
            less_m c zr  then  
                         wMon m . showString " - " . wr ((neg c, p): ms)
          else           wMon m . showString " + " . wr ((c, p)    : ms)

       (_,   m: ms        ) -> wMon m . showString " + " . wr ms

     wMon (c, pp) =
       let pp_str = wpp varDescr pp ""
       in
       case (unM, pp_str)
       of
       (_,       []) -> dShows opt' c
       (Nothing, _ ) -> dShows opt' c . showChar '*' . showString pp_str
       (Just un, _ ) -> if c == un then  showString pp_str
                        else   
                        dShows opt' c . showChar '*' . showString pp_str

     wpp :: FAAVarDescr -> [(Z, Z)] -> String -> String
                                          -- writing `power product'
     wpp _  []           = id
     wpp vd ((x, e): pp) = 
       case 
           (e > 0, fits x $ fst vd, fst $ snd vd) 
       of
       (False, _,     _     ) -> 
                            error $ msg $ msg' 
                            "non-positive exponent for some variable.\n"
       (_,     False, _     ) -> error $ msg $ msg'
                                        "variable index out of range.\n"
       (_,     _,     vToStr) ->
         case 
             (vToStr x, e, pp)
         of
         (Nothing,  _, _ ) -> error $ msg $ msg' ("unprintable variable\
                                         \ index:  " ++ (shows x ".\n"))
         (Just str, 1, []) -> showString str
         (Just str, 1, pp) -> showString str . showChar '*' . wpp vd pp
         (Just str, n, []) -> showString str . showChar '^' . shows n
         (Just str, n, pp) -> showString str . showChar '^' . shows n . 
                              showChar '*' . wpp vd pp

     fits x (Just n) = 0 < x && x <= n
     fits x _        = 0 < x 


------------------------------------------------------------------------
instance CommutativeRing a => Set (FAA a)
  where
  compare_m = compareTrivially
  fromExpr  = fromexpr_
  showsDomOf verb f =  showString "FAA(" . showsn verb (faaN f) . 
                       showChar ',' . showsDomOf 1 (sample f) . 
                                                            showChar ')'
  baseSet _ _ = error "\nbaseSet (FAA ..):  to be implemented.\n"


fromexpr_ :: CommutativeRing a =>
                         FAA a -> Expression String -> ([FAA a], String)
-- LOCAL.
-- Parse from expression non-commutative polynomial given a sample one.
-- So far, it requires a ring `a' with UNITY.

fromexpr_ smp e =  
  case (unity $ sample smp, faaVarDescr smp) 
  of
  (u, vd) -> rd e
    where
    rd e = 
      case fromExpr u e   -- first try coefficient
      of   
      ([c], "") -> ([ctr smp c], "")
      _         ->
        (case  e  of
          E (L "-") []   [e2] -> rd' "-u" ([],"") (rd e2)
          E (L "-") [e1] [e2] -> rd' "-"  (rd e1) (rd e2)
          E (L "+") [e1] [e2] -> rd' "+"  (rd e1) (rd e2)
          E (L "*") [e1] [e2] -> rd' "*"  (rd e1) (rd e2)
          E (L "/") [e1] [e2] -> rd' "/"  (rd e1) (rd e2)
          E (L "^") [e1] [e2] -> pw (rd e1) (fromExpr (1 :: Integer) e2)
          L s                 -> variable s vd 
          _                   -> ([], msg "\n\nWrong expression.\n")
        )
        where
        msg = showString "\nfromExpr sampleFAA expr,\nsampleFAA =   " . 
              showsn 1 smp . showString "\n <-  " . showsDomOf 1 smp .
              showString "\nexpr =  " . showsn 1 e

        rd' "-u" _        ([f],"") = ([-f ], "")
        rd' "-"  ([f],"") ([g],"") = ([f-g], "")
        rd' "+"  ([f],"") ([g],"") = ([f+g], "")
        rd' "*"  ([f],"") ([g],"") = ([f*g], "")
        rd' "/"  ([f],"") ([g],"") = 
                 case divide_m f g 
                 of
                 Just q -> ([q], "")
                 _      -> ([],  msg "\n\nFailed to divide with `/'.\n")

        rd' _    ([_], "") pair     = pair
        rd' _    pair      _        = pair
 
        pw ([f], "" ) ([n], "" ) = ([f^n], "" )
        pw ([_], "" ) (_,   msg) = ([],    msg)
        pw (_,   msg) ([_], "" ) = ([],    msg)

                                       -- read nc-monomial from variable
        variable s (mn, (_, fromStr)) =
          case
              fromStr s   
          of
          Nothing -> 
                ([], msg ("\n\nUnreadable variable:  " ++ (s ++ ".\n")))

          Just i  -> ([ct smp (u, FreeM mn [(i, 1)])],  "")


------------------------------------------------------------------------
instance CommutativeRing a => AddSemigroup (FAA a)
  where
  add       = add_
  zero_m f  = Just $ ctr f $ zeroS $ sample f
  neg_m     = Just . neg_
  times_m f = Just . (times_ times f)

  baseAddSemigroup _ _ = error "\nbaseAddSemigroup (FAA ..):  to be \
                                                        \implemented.\n"

instance CommutativeRing a => AddMonoid (FAA a)
instance CommutativeRing a => AddGroup  (FAA a)
  where
  baseAddGroup _ _ = error "\nfinish  baseAddGroup (FAA ..).\n"
                
------------------------------------------------------------------------
instance CommutativeRing a => MulSemigroup (FAA a)
  where
  unity_m f = fmap (ct f) $ unity_m $ sample f
  mul   f g = case faaMons f of 
                          []   -> zeroS f
                          m: _ -> (fst $ faaMonFAAMul m g) + (pTail f)*g

  inv_m f = if  isZero f || not (pIsConst f)  then  Nothing
            else                              fmap (ct f) $ inv_m $ lc f

  divide_m f g =
               let zeroP = zeroS f
               in
               case (f == zeroP, g == zeroP)
               of
               (True, _   ) -> Just zeroP
               (_,    True) -> Nothing
               _            -> let (q, r) = pDivRem f g
                               in  if isZero r then Just q  else Nothing

  divide_m2 _ _ = error "\ndivide_m2  is not defined for ..=> FAA a,  \
                                                             \so far.\n"
  root _ _ = error "\nroot  is not defined for ..=> FAA a,  so far.\n"

  -- power  is the default

  baseMulSemigroup _ _ = error "\nbaseMulSemigroup (FAA ..) :  to be \
                                                        \implemented.\n"


instance (CommutativeRing a, MulMonoid a) => MulMonoid (FAA a)

instance CommutativeRing a => Num (FAA a)  
  where 
  negate = neg
  (+)    = add
  (-)    = sub
  (*)    = mul
  signum _ = error "\nsignum  is not defined for ..=> FAA a  \
                    \(non-commutative polynomials).\n"

  abs _ = error "\nabs  is not defined for ..=> FAA a  \
                                      \(non-commutative polynomials).\n"
  fromInteger _ = error "\nfromInteger  to (FAA _):  use  fromi, \
                                                   \fromi_m  instead.\n"

instance CommutativeRing a => Fractional (FAA a) 
  where
  (/)            = divide
  fromRational _ =  error "\nfromRational  to (FAA _):\ninstead use  \
                          \fromi, fromi_m  combined with  divide_m.\n"

instance CommutativeRing a => Ring (FAA a)
  where
  fromi_m  f   = fmap (ctr f) . fromi_m (sample f)
  baseRing _ _ = error "\nbaseRing (FAA ..):  to be implemented.\n"

