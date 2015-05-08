----------------------------------------------------------------------
----------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2011
----------------------------------------------------------------------
----------------------------------------------------------------------




module Categs   -- domain descriptions
  (
   UMon, Fraction(..), ResidueE(..), Subring(..),
   Properties_Subring, Property_Subring(..), 
   Construction_Subring(..), Operations_Subring, OpName_Subring(..),
   Operation_Subring(..),

   Dom(..), Domain1(..), Domain2(..), Domains1, Domains2,
   CategoryName(..), 

   Ideal(..), Properties_Ideal, Properties_IdealGen,
   Property_Ideal(..), Property_IdealGen(..),
   Construction_Ideal(..), Operations_Ideal, OpName_Ideal(..), 
   Operation_Ideal(..),

   Submodule(..), Properties_Submodule, Properties_SubmoduleGens,
   Operations_Submodule, Property_Submodule(..), 
   Property_SubmoduleGens(..), OpName_Submodule(..),
   Operation_Submodule(..), Construction_Submodule(..),

   LinSolvModuleTerm(..), Properties_LinSolvModule, 
   Property_LinSolvModule(..),


   -- from Categs_:

   Vector(..), vecRepr, PowerProduct, PPComp, AddOrMul(..), 
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

   FactrRingTerm(..), Properties_FactrRing, 
   Property_FactrRing(..), 

   LinSolvRingTerm(..), Properties_LinSolvRing, 
   Property_LinSolvRing(..), 

   EucRingTerm(..), Properties_EucRing, Property_EucRing(..)
  )
where
import qualified Data.Map as Map (Map(..)) 

import Prelude_ (PropValue(..), InfUnn(..), Natural, MMaybe)
import Categs_





------------------------------------------------------------------------
infixl 7  :/

data Fraction a =  a :/ a  deriving(Eq,Read)

instance Functor Fraction  where  fmap f (n:/d) = (f n):/(f d)

type UMon a = (a, Integer)                        -- univariate monomial

data {- EuclideanRing a => -}
                        ResidueE a = Rse a (PIRChinIdeal a) (Domains1 a)
  --
  -- Element of  a/I,  `a' an Euclidean ring. 
  -- See Manual, ResEuc0_.hs

------------------------------------------------------------------------
data Subring a =  
     Subring {subringChar    :: (Maybe Natural),
              subringGens    :: (Maybe [a]),
              subringProps   :: (Properties_Subring),
              subringConstrs :: [Construction_Subring a],
              subringOpers   :: (Operations_Subring a)
             }
type Properties_Subring = [(Property_Subring,PropValue)]
data Property_Subring   =                                  -- see manual

       IsField | HasZeroDiv | HasNilp | IsPrimaryRing | Factorial
     | PIR | IsOrderedRing | IsRealField | IsGradedRing
     deriving(Eq, Ord, Enum, Show)
                           -- IsGradedRing  refers to Operations_Subring

data Construction_Subring a = ConsRingDUMMY  deriving (Show)
                              -- Intersection_Subring [Subring a]
                              -- | GenBySet_Subring     (OSet a)
                              -- | DirectSum_Subring    [Subring a]
                              --        requires Commutative==Yes
      
type Operations_Subring a = [(OpName_Subring, Operation_Subring a)]

data OpName_Subring = WithPrimeField -- | ...
                                          deriving (Eq, Ord, Enum, Show)
data Operation_Subring a = 
     WithPrimeField'
              {frobenius            :: (a -> a, a -> MMaybe a),
               dimOverPrime         :: InfUnn Natural, 
               primeFieldToZ        :: a -> Integer,
               primeFieldToRational :: a -> Fraction Integer,
               primitiveOverPrime   :: ([a], [UMon a], a -> [UMon a])}
      -- | ...
  -- see  Manual 'rg.sub'.

------------------------------------------------------------------------
type Domains1 a   = Map.Map CategoryName (Domain1 a)
type Domains2 a b = Map.Map CategoryName (Domain2 a b)

data CategoryName = 
     Set | AddSemigroup | AddGroup | MulSemigroup | MulGroup | Ring |
     LinSolvRing | GCDRing  | FactorizationRing | EuclideanRing | 
     IdealKey | LeftModule | LinSolvLModule
     -- ...
     deriving (Eq, Ord, Enum, Show)


data Domain1 a =    D1Set      (OSet            a)   
                  | D1Smg      (Subsemigroup    a)  
                  | D1Group    (Subgroup        a)  
                  | D1Ring     (Subring         a)  
                  | D1GCDR     (GCDRingTerm     a)  
                  | D1FactrR   (FactrRingTerm   a)  
                  | D1LinSolvR (LinSolvRingTerm a)  
                  | D1EucR     (EucRingTerm     a)  
                  | D1Ideal    (Ideal           a)  
                  -- ...

data Domain2 a b =    D2Module   (Submodule a b)   
                    | D2LinSolvM (LinSolvModuleTerm a b)
                    -- ...
class Dom c  
  where  
  dom    :: c a -> Domains1 a   -- domain over which the constructor
                                -- c  acts  - the argument domain
  sample :: c a -> a       -- sample element for the argument domain

  -- Examples: 
  -- for  f = UPol _ 0 _ dZ   - univariate polynomial over Integer -
  --                                    dom f = dZ,  sample f = 0;
  -- for  r = Rse 2 iI dZ     - residue modulo I of Integer -
  --                                    dom r = dZ,  sample f = 2;


----------------------------------------------------------------------
data Ideal a = Ideal {idealGens     :: (Maybe [a]),
                      idealProps    :: Properties_Ideal,
                      idealGenProps :: Properties_IdealGen,
                      idealConstrs  :: [Construction_Ideal a],
                      idealOpers    :: (Operations_Ideal a)}
                                                   deriving (Show)

type Properties_Ideal    = [(Property_Ideal,    PropValue)]
type Properties_IdealGen = [(Property_IdealGen, PropValue)]

data Property_Ideal    = IsMaxIdeal | Prime | Primary
                                      deriving (Eq, Ord, Enum, Show)
data Property_IdealGen = IsGxBasis    deriving (Eq, Ord, Enum, Show)

newtype Construction_Ideal a = GenFactorizations [Factorization a]
                                                 deriving (Show)

-- | IdealIntersection [Ideal a] | IdealSum          [Ideal a]
-- | IdealProduct      [Ideal a] | IdealQuotient     (Ideal a) (Ideal a)

-- GenFactorizations  is only for the Factorial ring;
-- In (GenFactorizations fts),  fts  is either [] or  (map factor gens).
-- Still `factor'  may return [] for some elements  - if
-- WithFactor /= Yes.  See `factor' of FactorizationRing.

type Operations_Ideal a = [(OpName_Ideal, Operation_Ideal a)]
data OpName_Ideal = IdealRank  deriving (Eq, Ord, Enum, Show)

newtype Operation_Ideal a = IdealRank' (InfUnn Natural) 
                                               deriving (Eq, Show)

------------------------------------------------------------------------
data Submodule r a = 
     Submodule {moduleRank     :: (InfUnn Natural),
                moduleGens     :: (Maybe [a]),
                moduleProps    :: Properties_Submodule,
                moduleGenProps :: Properties_SubmoduleGens,
                moduleConstrs  :: [Construction_Submodule r a],
                moduleOpers    :: (Operations_Submodule r a)}
-- see Manual

type Properties_Submodule     = [(Property_Submodule,PropValue)]
type Properties_SubmoduleGens = [(Property_SubmoduleGens, PropValue)]
type Operations_Submodule r a = 
                           [(OpName_Submodule, Operation_Submodule r a)]
data Property_Submodule = 
                  IsFreeModule   | IsPrimeSubmodule | IsPrimarySubmodule 
                | IsMaxSubmodule | HasZeroDivModule | IsGradedModule 
                deriving (Eq, Ord, Enum, Show)
                -- these properties generalize, as usual, the ring 
                -- (or ideal) ones

data Property_SubmoduleGens = IsFreeModuleBasis | IsGxBasisM 
                                          deriving (Eq, Ord, Enum, Show)

data OpName_Submodule        = GradingM deriving (Eq, Ord, Enum, Show)
data Operation_Submodule r a = GradingM' PPComp (a -> PPComp) (a -> [a])
data Construction_Submodule r a = ConsModuleDUMMY  deriving (Show)
                         
                       -- DProduct_Submodule     [Submodule r a]
                       -- | Intersection_Submodule [Submodule r a]
                       -- ...
------------------------------------------------------------------------
data LinSolvModuleTerm r a =
     LinSolvModuleTerm {linSolvModuleProps :: Properties_LinSolvModule}
                        -- what else?
                       deriving (Show)

type Properties_LinSolvModule = [(Property_LinSolvModule,PropValue)]
data Property_LinSolvModule =
      IsCanAssocModule | ModuloBasisDetaching_M | ModuloBasisCanonic_M |
      WithSyzygyGens_M | IsGxModule 
                                          deriving (Eq, Ord, Enum, Show)
  -- (IsCanAssocModule, Yes)  means that the ring is commutative,
  -- canAssocM _ v  is a unique vector chosen among
  --                               {c*v :  c  is the invertible factor},
  -- canInvM _ v    is the relevant factor.
  -- Other properties are similar to the corresponding Ring ones.




{- reserve *******************************************************
Opers ..  | Grading' cp weight forms  ...

A graded ring must have unity.
In  Grading' cp weight forms,
 cp      is the admissible ordering on Z^n (as for polynomials),
         so (n,cp)  defines an ordered additive group structure
         on  Z^n.
         It is known that any grading monoid for the graded
         ring is equivalent to  Z^n  defined by some  n, cp.
         The value of  n  can be obtained by applying, say,
         genLength (weight unity).
 weight  is the grading weight homomorphism  (a,*) -> (Z^n,+)
 forms a  ->  [a1..am],    a = a1+...+am,
         is the (unique) grading decomposition into the sum of
         the homogeneous forms with respect to the grading given
         by  cp, weight.
  ********************************************************
-}
