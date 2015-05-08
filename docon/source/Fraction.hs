------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------




module Fraction    -- see  manual.`fr' and Fract_.hs  for prelude

  (Fraction(..),                           -- from Ring0_
   num, denom, zeroFr, unityFr, canFr      -- from Fract_

   -- ,instances for Fraction a: 
   -- Functor, Dom, ... OrderedSet ... RealField, OrderedField
   -- - some of them imported from Fract_, Ring0_
   --
   -- Specializations for some instances for  Fraction Z.
  )
where
import qualified Data.Map as Map (empty, lookup, insert)

import DPrelude (PropValue(..), InfUnn(..))
import Categs  
import SetGroup 
import Ring0_   
import LinAlg (solveLinear_euc)
import Fract_ (canFr, zeroFr, unityFr, num, denom)

import qualified Fract_ (cmp_, add_, pow_, mul_, fromexpr_)




------------------------------------------------------------------------
ifGCDRing :: GCDRing a => a -> b -> String -> (b, c) -> (b, c)  -- LOCAL
ifGCDRing                 a    dom  message   v =  
  (case 
       isGCDRing $ snd $ baseGCDRing a Map.empty
   of
   No -> (dom, error (message ++ msg))
   _  -> v
  )
  where  
  msg = "gcd-ring R needed to operate in  Fraction R,\nR =  " ++ 
        (showsDomOf 1 a ".\n") 

------------------------------------------------------------------------
instance GCDRing a => GCDRing (Fraction a)  
  where
  -- Fraction a  is a Field. 
  -- So the GCDRing operations are trivial for it.

  canAssoc (n:/d) = if n == zeroS d  then zeroFr d   else unityFr d
  canInv   (n:/d) = if n == zeroS d  then unityFr d  else n:/d

  gcD []           = error "gcD [] \n"
  gcD ((n:/d): fs) = if  n == zeroS d  then  gcD fs  else  unityFr d

  hasSquare _ = 
       error "\nhasSquare  is senseless for  GCDRing a => Fraction a.\n"
  toSquareFree _ = 
          error 
          "\ntoSquareFree  is senseless for  GCDRing a => Fraction a.\n"

  baseGCDRing (n :/ _) dom =  
    case  
        Map.lookup GCDRing dom  
    of
    Just (D1GCDR t) -> (dom, t)
    _               -> 
                     ifGCDRing n dom "baseGCDRing (_ :/ _):  " (dom', t)
           where
           dom' = Map.insert GCDRing (D1GCDR t) dom
           t    = GCDRingTerm
                  {gcdRingProps = [(WithCanAssoc, Yes), (WithGCD, Yes)]}
               
------------------------------------------------------------------------
instance GCDRing a => FactorizationRing (Fraction a)  
  where
  -- Fraction a  is a Field. 
  -- So the below operations are trivial for it.

  isPrime _ = False
  factor  _ = []
  primes  _ = []

  baseFactrRing (n :/ _) dom = 
    case 
        Map.lookup FactorizationRing dom  
    of
    Just (D1FactrR t) -> (dom, t)
    _                 ->
                   ifGCDRing n dom "baseFactrRing (_ :/ _):  " (dom', t)
        where
        dom'  = Map.insert FactorizationRing (D1FactrR t) dom
        t     = FactrRingTerm {factrRingProps = props}
        props = 
           [(WithIsPrime, Yes), (WithFactor, Yes), (WithPrimeList, Yes)]

------------------------------------------------------------------------
instance GCDRing a => LinSolvRing (Fraction a)   
  where
  -- Fraction a  is a Field. 
  -- So the the below operations are trivial for it.

  moduloBasis _ []           y = (y, [])
  moduloBasis _ ((n:/d): fs) y = (z,  (y/(n:/d)): (map (const z) fs))
                                                       where
                                                       z = zeroFr d
  gxBasis []           = ([], [])
  gxBasis ((n:/d): fs) = let {z = zeroFr d;  i = inv (n:/d)}
                         in
                         ([unityFr d], [i:(map (const z) fs)])

  syzygyGens mode [] = error ("\nsyzygyGens " ++ (mode ++ " [].\n"))
  syzygyGens _    xs = snd $ solveLinear_euc [xs] [z] 
                                                  where  
                                                  z = zeroS $ head xs

  baseLinSolvRing (n :/ _) dom = 
    case 
        Map.lookup LinSolvRing dom  
    of
    Just (D1LinSolvR t) -> (dom, t)
    _                   ->
                 ifGCDRing n dom "baseLinSolvRing (_ :/ _):  " (dom', t)
        where
        dom'  = Map.insert LinSolvRing (D1LinSolvR t) dom
        t     = LinSolvRingTerm {linSolvRingProps = props}
        props = [(ModuloBasisDetaching, Yes), (ModuloBasisCanonic, Yes),
                 (WithSyzygyGens,       Yes), (IsGxRing,           Yes)]

------------------------------------------------------------------------
instance GCDRing a => EuclideanRing (Fraction a)  
  where
  -- Fraction a  is a Field. 
  -- So the the below operations are trivial for it.

  eucNorm f = 
    if  
      isZero f then  
               error ("\neucNorm 0: \n0 <- " ++ (showsDomOf 1 f ".\n"))
    else       0

  divRem _ (n:/d) y =  ((n:/d)/y, zeroFr d)

  baseEucRing (n :/ _) dom =  
    case  
        Map.lookup EuclideanRing dom  
    of
    Just (D1EucR t) -> (dom, t)
    _               ->
                     ifGCDRing n dom "baseEucRing (_ :/ _):  " (dom', t)
          where
          dom'  = Map.insert EuclideanRing (D1EucR t) dom
          t     = EucRingTerm {eucRingProps = props}
          props = [(Euclidean, Yes), (DivRemCan, Yes), (DivRemMin, Yes)]

------------------------------------------------------------------------
instance GCDRing a                  => Field (Fraction a)
instance (GCDRing a, OrderedRing a) => RealField (Fraction a)   
instance (GCDRing a, OrderedRing a) => OrderedField (Fraction a)   

------------------------------------------------------------------------
-- Specialisation:  Fraction Integer = RationalNumber

instance Set (Fraction Integer)    
  where 
  compare_m      = Fract_.cmp_
  showsDomOf _ _ = showString "(Fr Z)"
  fromExpr f     = Fract_.fromexpr_ (num f) 

  baseSet _ dom = (Map.insert Set (D1Set s) dom, s)
    where                                   
    s = OSet 
        {osetSample  = 0:/1,     membership  = belongs,
         osetCard    = Infinity, osetPointed = Just $ Just $ (0:/1),
         osetList    = Nothing,  osetBounds  = bounds,
         osetProps   = props,   
         osetConstrs = [(Interval Nothing False Nothing False)],
         osetOpers   = []
        }                               
    belongs _ (n:/d) =  d > 0  &&  (abs $ gcd n d) == 1 

    props  = [(IsBaseSet   , Yes), (FullType      , No), 
              (Finite      , No ), (OrderIsTrivial, No), 
              (OrderIsTotal, Yes), (OrderIsNoether, No),
              (OrderIsArtin, No )
             ]
    bounds = (Just Nothing, Just Nothing, Just Nothing, Just Nothing)


------------------------------------------------------------------------
instance AddSemigroup (Fraction Integer)   
  where
  zero_m  _        = Just (0:/1)
  neg_m   (n:/d)   = Just ((-n) :/ d)
  add              = Fract_.add_ 
  sub_m   x      y = Just $ add x $ neg y
  times_m (n:/d) k = Just ((n*(k/g)) :/ (d/g))  where g = abs $ gcd d k

  baseAddSemigroup _ dom = (Map.insert AddSemigroup (D1Smg s) dom, s)
    where
    s = Subsemigroup 
         {subsmgType    = Add,     subsmgUnity = Just $ Just (0:/1),
          subsmgGens    = Nothing, subsmgProps = props,
          subsmgConstrs = [],      subsmgOpers = []
         }
    props = [(Commutative,           Yes), (IsGroup, Yes),  
             (IsMaxSubsemigroup,     No ), 
             (IsCyclicSemigroup,     No ), -- so far
             (IsOrderedSubsemigroup, Yes)]
 
------------------------------------------------------------------------
instance AddGroup (Fraction Integer) 
  where
  baseAddGroup _ dom = (Map.insert AddGroup (D1Group g) dom, g)
    where
    g = Subgroup
        {subgrType    = Add,                  subgrGens  = Nothing,
         subgrCanonic = Just $ const (0:/1),  subgrProps = props,
         subgrConstrs = [],                   subgrOpers = []
        }                           
    props = [(IsNormalSubgroup , Yes), (IsMaxSubgroup, No), 
             (IsOrderedSubgroup, Yes), (IsCyclicGroup, No),
             (IsPrimeGroup,      No )]

--------------------------------------------------------------------
instance MulSemigroup (Fraction Integer)   
  where
  unity_m _    = Just (1:/1)
  inv_m (n:/d) = case compare n 0 of EQ -> Nothing
                                     GT -> Just (d:/n)
                                     _  -> Just ((-d):/(-n))
  mul     = Fract_.mul_
  power_m = Fract_.pow_

  divide_m (0:/_) _      = Just (0:/1)
  divide_m _      (0:/_) = Nothing
  divide_m x      y      = Just $ mul x $ inv y

  divide_m2 _ _ = 
         error "\ndivide_m2  for  Fraction Integer :   use  divide_m.\n"

  root deg (n:/d) = 
       case (root deg n, root deg d) 
       of 
       (Just (Just r1), Just (Just r2)) -> Just (Just (canFr "i" r1 r2))
       (Just Nothing,   _             ) -> Just Nothing
       (_,              Just Nothing  ) -> Just Nothing
       _                                -> Nothing       -- ?

  baseMulSemigroup _ dom = (Map.insert MulSemigroup (D1Smg s) dom, s)
    where
    s = Subsemigroup 
        {subsmgType    = Mul,      subsmgUnity  = Just $ Just (1:/1),
         subsmgGens    = Nothing,  subsmgProps  = props,
         subsmgConstrs = [],       subsmgOpers = []
        }                          
    props = [(Commutative,          Yes), (IsGroup          , No),
             (IsCyclicSemigroup,    No ), (IsMaxSubsemigroup, No),
             (IsOrderedSubsemigroup,Yes)]

------------------------------------------------------------------------
instance Ring (Fraction Integer) 
  where 
  fromi_m _ k = Just (k:/1)

  baseRing _ dom = (Map.insert Ring (D1Ring r) dom, r)
    where
    r = Subring {subringChar  = Just 0,  subringGens    = Nothing,
                 subringProps = props,   subringConstrs = [],
                 subringOpers = []
                }
    props = [(IsField,       Yes), (Factorial,   Yes),  
             (HasZeroDiv,    No ), (HasNilp,     No ),
             (IsPrimaryRing, Yes), (PIR,         Yes),
             (IsOrderedRing, Yes), (IsRealField, Yes),
             (IsGradedRing,  Yes)]
