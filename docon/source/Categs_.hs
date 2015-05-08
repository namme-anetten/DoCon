--------------------------------------------------------------------
--------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
--------------------------------------------------------------------
--------------------------------------------------------------------





module Categs_     

  -- Domain descriptions
  --
  -- All needed from here is  reexported by  Categs.


  (Vector(..), vecRepr, PowerProduct, PPComp, AddOrMul(..),
   PIRChinIdeal(..), Factorization,

   OSet(..), Properties_OSet, Property_OSet(..),
   Construction_OSet(..), Operations_OSet, OpName_OSet(..),
   Operation_OSet(..), 

   Subsemigroup(..), Properties_Subsemigroup,
   Property_Subsemigroup(..), Construction_Subsemigroup(..),
   Operations_Subsemigroup, OpName_Subsemigroup(..),
   Operation_Subsemigroup(..), 

   Subgroup(..), Properties_Subgroup, Property_Subgroup(..), 
   Construction_Subgroup(..), Operations_Subgroup, 
   OpName_Subgroup(..), Operation_Subgroup(..),

   GCDRingTerm(..), Properties_GCDRing, Property_GCDRing(..),

   FactrRingTerm(..), Properties_FactrRing, Property_FactrRing(..), 

   LinSolvRingTerm(..), Properties_LinSolvRing, 
   Property_LinSolvRing(..), 

   EucRingTerm(..), Properties_EucRing, Property_EucRing(..)
  )

where
import Prelude_ (InfUnn(..), PropValue, MMaybe, Z, Comparison)




------------------------------------------------------------------------
newtype Vector a = Vec [a] deriving(Eq)   -- non-empty list boxed in Vec
vecRepr (Vec l) = l

type Factorization a = [(a, Z)]
  -- Example:
  -- 8*49*3 = 2^3*7^2*3
  -- expresses as  [(2,3),(7,2),(3,1)]  :: Factorization Z

type PowerProduct = Vector Z
type PPComp       = Comparison PowerProduct  -- power product comparison
------------------------------------------------------------------------
data PIRChinIdeal a = 
  PIRChinIdeal
    {pirCIBase      :: a,                 -- b:  Ideal = (b)
     pirCICover     :: [a],               -- bs: (b) = intersect[..]
     pirCIOrtIdemps :: [a],               -- es: idempotents
     pirCIFactz     :: (Factorization a)  -- ft = [(p1,m1)..(pw,mw)]
    }
  deriving (Show, Read)    -- see manual.

  {- Special representation for non-trivial ideal I in a Principal
     Ideal ring.
     * b  is NOT zero and NOT invertible
     * If  bs==[]    then  es==[]
     * If  bs /= []  then
         (b) = idealIntersection [(bj) | bj <- bs],
         (bi)+(bj) = (1)  for any  i/=j  (reciprocally prime ideals)
     * If  es /= []  then
         es = [e1..ew], ei<-`a' are Lagrange orthogonal idempotents:
                          ei modulo bj = 1, for i==j,  0, otherwise,
                          - hence  ei^2 = ei,  e1 +..+ ew = 1
     * If  ft /= []  then
         `a'  is a factorial ring,
         ft = [(p1,m1)..(pw,mw)]  is factorization of b to primes:
                               b = product bs,  bi=pi^mi,  i<-[1..w]
                               (bi and pi listed in the same order).
  -}

------------------------------------------------------------------------
data OSet a =
     OSet {osetSample  :: a,                      -- sample for Base set
           membership  :: Char -> a -> Bool,
           osetCard    :: (InfUnn Z),  -- cardinality
           osetPointed :: (MMaybe a),  -- pointed element in subset
           osetList    :: (Maybe [a]),  
           osetBounds  :: (MMaybe a,MMaybe a,MMaybe a,MMaybe a),
           osetProps   :: Properties_OSet,
           osetConstrs :: [Construction_OSet a],
           osetOpers   :: (Operations_OSet a)
          }
type Properties_OSet = [(Property_OSet,PropValue)]
data Property_OSet   =
                      Finite | FullType | IsBaseSet
                    | OrderIsTrivial | OrderIsTotal | OrderIsNoether
                    | OrderIsArtin
                    -- | OrderIsDedekind | OrderIsComplete
                    --                           (like for Ordinals) - ?
                    deriving(Eq,Ord,Enum,Show)

data Construction_OSet a = Interval (Maybe a) Bool (Maybe a) Bool
                                                         deriving (Show)
                               -- | Union [OSet a]  
                               -- | Intersection [OSet a] ...

type Operations_OSet a = [(OpName_OSet, Operation_OSet a)]

  -- DUMMY, so far.

data OpName_OSet       = OpN_OSet_DUMMY  deriving(Eq,Show)
data Operation_OSet a  = Op_OSet_DUMMY   deriving(Show)

  -- See  manual.txt  for examples.


------------------------------------------------------------------------
-- Subsemigroup H  is considered relatively to the base semigroup G.
-- See below the semigroup classes.


data Subsemigroup a =
     Subsemigroup {subsmgType    :: AddOrMul,  -- operation name
                   subsmgUnity   :: (MMaybe a),
                   subsmgGens    :: (Maybe [a]),
                   subsmgProps   :: Properties_Subsemigroup,
                   subsmgConstrs :: [Construction_Subsemigroup a],
                   subsmgOpers   :: (Operations_Subsemigroup a)
                  }

data AddOrMul = Add | Mul  deriving(Eq,Show,Ord,Enum)


  -- ..Gens = []  means "unknown"

  -- See  manual.txt.

type Properties_Subsemigroup = [(Property_Subsemigroup,PropValue)]
data Property_Subsemigroup   =

            Commutative | IsCyclicSemigroup | IsGroup | IsMaxSubsemigroup
          | IsOrderedSubsemigroup
          deriving (Eq, Ord, Enum, Show)

    -- IsOrderedSubsemigroup==Yes   means that
    --
    -- 1. Commutative == Yes
    -- 2. compare_m  (of Set)   is a total order on This  sset
    --                          (IsTotalOrder==Yes)  agreed with
    --                          `add' (mul), zero_m (unity_m).

data Construction_Subsemigroup a = ConsSemigDUMMY  deriving(Show)

                          --  Intersection_Subsemigroup [Subsemigroup a]
                          -- | GenBySet_Subsemigroup     (OSet a)
                  
type Operations_Subsemigroup a =
                       [(OpName_Subsemigroup, Operation_Subsemigroup a)]

data OpName_Subsemigroup      = OpNSemigDUMMY  deriving(Eq, Show)
data Operation_Subsemigroup a = OpSemigDUMMY'  deriving(Show)



------------------------------------------------------------------------
-- Subgroup H of a group G:


data  {-Add(Mul)Group a=>-}  Subgroup a =

  Subgroup {subgrType    :: AddOrMul,
            subgrGens    :: (Maybe [a]),
            subgrCanonic :: Maybe (a -> a),
            subgrProps   :: Properties_Subgroup,
            subgrConstrs :: [Construction_Subgroup a],
            subgrOpers   :: (Operations_Subgroup a)
           }
  -- unity, zero   are obtained by applying (unity x) or (zeroS x)
  --
  -- ..Gens =   Nothing    (unknown)  
  --          | Just gs,   gs  a finite list of the group 
  --                       generators for H.
  --
  -- ..Canonic =  Nothing | Just canf,
  --         the latter means that  canf: G -> G
  --         is a canonical map for the congruence classes x*H:
  --           canf(x) - x <- H               &
  --           x-y <- H <=> canf(x)=canf(y)   &
  --           canf(zero+H) = zero
  --         - similar *-denotations are for the Mul case.

type Properties_Subgroup = [(Property_Subgroup,PropValue)]
data Property_Subgroup   =
                IsCyclicGroup | IsPrimeGroup | IsNormalSubgroup
              | IsMaxSubgroup | IsOrderedSubgroup
              deriving(Eq,Ord,Enum,Show)

         -- IsOrderedSubgroup==Yes   means that
         --
         -- 1. the  subsemigroup  has  (IsOrderedSubsemigroup,Yes)
         -- 2. compare_m          agrees with  `neg' (`inv')

data Construction_Subgroup a = ConsGroupDUMMY  deriving(Show)
                               -- Intersection_Subgroup [Subgroup a]
                               -- | GenBySet_Subgroup (OSet a)

type Operations_Subgroup a = [(OpName_Subgroup, Operation_Subgroup a)]
data OpName_Subgroup       = OpNGroupDUMMY  deriving (Eq, Show)
data Operation_Subgroup a  = OpGroupDUMMY   deriving (Show)

------------------------------------------------------------------------
data GCDRingTerm a = GCDRingTerm {gcdRingProps:: Properties_GCDRing
                                  -- what else?
                                 }
                                 deriving (Show)

type Properties_GCDRing = [(Property_GCDRing, PropValue)]

data Property_GCDRing   = WithCanAssoc | WithGCD
                                           deriving(Eq, Ord, Enum, Show)
  -- WithCanAssoc=Yes  ===
  --                canAssoc, canInv,  are the correct algorithms for
  --                the canonical associated element and the canonical
  --                invertible factor
  -- WithGCD=Yes ===
  --        (Factorial, Yes) &
  --        gcD is the correct algorithm for the greatest common divisor


data FactrRingTerm a =
     FactrRingTerm {factrRingProps :: Properties_FactrRing
                    -- what else?
                   }
                   deriving(Show)

type Properties_FactrRing = [(Property_FactrRing,PropValue)]

data Property_FactrRing = WithIsPrime | WithFactor | WithPrimeList
                          deriving (Eq, Ord, Enum, Show)

  -- WithIsPrime=Yes ===  isPrime  is the correct primality test
  -- WithFactor=Yes  ===  factor   is the correct factorization
  -- WithPrimeList   ===  primes   is the described above list

data LinSolvRingTerm a =
     LinSolvRingTerm {linSolvRingProps :: Properties_LinSolvRing
                      -- what else?
                     }
                     deriving(Show)

type Properties_LinSolvRing = [(Property_LinSolvRing,PropValue)]
data Property_LinSolvRing   =
                            ModuloBasisDetaching | ModuloBasisCanonic |
                            WithSyzygyGens | IsGxRing
                                           deriving(Eq, Ord, Enum, Show)

data EucRingTerm a = EucRingTerm {eucRingProps :: Properties_EucRing
                                  -- what else?
                                 }
                                 deriving(Show)

type Properties_EucRing = [(Property_EucRing, PropValue)]

data Property_EucRing   = Euclidean | DivRemCan | DivRemMin
                                           deriving(Eq, Ord, Enum, Show)
