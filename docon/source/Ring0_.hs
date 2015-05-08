------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------





module Ring0_    -- Ring... GCDRing... Field categories;  related items;
                 -- Fraction, Matrix  data.
                 -- All needed from here is  reexported by  RingModule.

(MatrixLike(..), -- class
 Matrix(..),     -- , instance Eq a => Eq (Matrix a) .., 

 Ring(..), CommutativeRing(), OrderedRing(), GCDRing(..), 
 FactorizationRing(..), LinSolvRing(..), EuclideanRing(..), Field(), 
 RealField(), OrderedField(),

 fromi, char, property_Subring_list, isField, isOrderedRing, 
 dimOverPrimeField, isPrimeIfField, props_Subring_zero, zeroSubring, 
 isGCDRing, isRingWithFactor, isGxRing, isEucRing, isCEucRing,

 upRing, upGCDRing, upFactorizationRing, upLinSolvRing, upEucRing, 
 upField, upGCDLinSolvRing, upEucFactrRing, upFactrLinSolvRing,

 isFactorizOfPrime, isFactorizOfPrimary, rankFromIdeal, isMaxIdeal, 
 isPrimeIdeal, isPrimaryIdeal, genFactorizationsFromIdeal, zeroIdeal, 
 unityIdeal
)
where
import qualified Data.Map as Map (empty)

import Data.Maybe  (fromMaybe)
import Data.List  (transpose)

import DPrelude (Natural, PropValue(..), InfUnn(..),  not3, lookupProp, 
                                                   mapmap, showsWithDom)
import Categs
import SetGroup 





------------------------------------------------------------------------
class MatrixLike m where                     -- for Matrix, SquareMatrix
                   mtRows :: m a -> [[a]]
                   mapMt  :: (a -> a) -> m a -> m a
                   transp :: m a -> m a                    

data Matrix a = Mt [[a]] (Domains1 a)

instance Eq a => Eq (Matrix a) where  x == y =  mtRows x == mtRows y

-- It should be   instance (MatrixLike m, Eq a) => Eq (m a) ...
-- but this overlaps with (Residue r,Eq a)=> Eq (r a)  in a strange way.

instance MatrixLike Matrix where mtRows (Mt rs _)  = rs
                                 transp (Mt rs d)  = Mt (transpose rs) d
                                 mapMt f (Mt rs d) = Mt (mapmap f  rs) d

------------------------------------------------------------------------
class (AddGroup a, MulSemigroup a, Num a, Fractional a) => Ring a  
  where
  -- presumed:
  -- non-zero  baseAddSemigroup A  and  baseMulSemigroup H have
  -- the same base set,  and  (+) = add, (*) = mul  obey the ring 
  -- laws.
  -- (/) = divide.

  baseRing :: a -> Domains1 a -> (Domains1 a, Subring a)

  fromi_m  :: a -> Integer -> Maybe a   
                               -- standard homomorphism from integer

  fromi_m x n = maybe Nothing (\ u -> times_m u n) $ unity_m x

------------------------------------------------------------------------
fromi :: Ring a => a -> Integer -> a                               -- sa
fromi x n =  fromMaybe (error msg) $ fromi_m x n
  where
  msg = showString "\nfromi x " $ shows n $ showsWithDom 1 x "x" "" "\n"
        
char :: Ring a => a -> Maybe Natural
char a =  subringChar $ snd $ baseRing a Map.empty

------------------------------------------------------------------------
class Ring a => CommutativeRing a     

  -- Presumed:  Commutative == Yes  
  --            for the base multiplicative semigroup

class (CommutativeRing a, OrderedAddGroup a) => OrderedRing a
  --
  -- Presumed:  IsOrderedRing == Yes  for the base ring
  --                                  (see Subring)

property_Subring_list = [IsField ..]

------------------------------------------------------------------------
isField,isOrderedRing :: Subring a -> PropValue

isField = lookupProp IsField . subringProps

dimOverPrimeField :: Subring a -> InfUnn Natural
dimOverPrimeField rR = case  lookup WithPrimeField $ subringOpers rR
                       of
                       Just w -> dimOverPrime w
                       _      -> UnknownV

isPrimeIfField :: Subring a -> PropValue
isPrimeIfField rR =  case dimOverPrimeField rR of Fin 1    -> Yes
                                                  UnknownV -> Unknown
                                                  _        -> No

isOrderedRing = lookupProp IsOrderedRing . subringProps

props_Subring_zero :: Properties_Subring
props_Subring_zero =  map setValue property_Subring_list
                                            where  
                                            setValue PIR = (PIR, Yes)
                                            setValue x   = (x,   No )
------------------------------------------------------------------------
                                   -- zero subring in a Non-zero ring rR
zeroSubring :: a -> Subring a -> Subring a
zeroSubring    zr   _ =   Subring {subringChar    = Just 0,
                                   subringGens    = Just [zr],
                                   subringProps   = props_Subring_zero,
                                   subringConstrs = [],
                                   subringOpers   = []}

------------------------------------------------------------------------
class (CommutativeRing a, MulMonoid a) => GCDRing a  
  where
  -- presumed: (HasZeroDiv, No) 

  baseGCDRing  :: a -> Domains1 a -> (Domains1 a, GCDRingTerm a)
  canAssoc     :: a -> a            -- canonical associated element
  canInv       :: a -> a            -- canonical invertible factor
  gcD          :: [a] -> a          -- gcd,lcm  are for a list
  lcM          :: [a] -> a
  hasSquare    :: a -> Bool         -- "has a multiple prime factor"
  toSquareFree :: a -> Factorization a
         --
         -- returns [(a,1)..(am,m)]:  (canAssoc a) = a1^1*..*am^m,
         -- each  ai  is square free  and  gcd(ai,aj) = 1  for i/=j,
         -- invertible  ai  are skipped, 
         --   in particular, [] is returned for invertible  a.

  canAssoc x = x/(canInv x)       

  lcM []     = error "lcM [] \n"
  lcM [x]    = x
  lcM [x,y]  = y*( x/(gcD [x,y]) )
  lcM (x:xs) = lcM [x, lcM xs]

  -- the correctness of these operations depend on the
  -- WithCanAssoc,WithGCD  values - see below

isGCDRing :: GCDRingTerm a -> PropValue
isGCDRing = lookupProp WithGCD . gcdRingProps

------------------------------------------------------------------------
class GCDRing a => FactorizationRing a       -- presumed: (WithGCD, Yes)
  where
  baseFactrRing :: a -> Domains1 a -> (Domains1 a, FactrRingTerm a)

  isPrime :: a -> Bool           
  factor  :: a -> Factorization a 
  primes  :: a -> [a]
       -- an infinite list of primes p(i) containing no repetitions,
       -- each p(i) in canAssoc form;  returns [] for the fail.
       -- It depends on the domain only, the argument is the sample 
       -- for the domain.

  isPrime x = case factor x of [(_, 1)] -> True
                               _        -> False

isRingWithFactor :: FactrRingTerm a -> PropValue
isRingWithFactor = lookupProp WithFactor . factrRingProps

------------------------------------------------------------------------
-- Ring with the solvable linear equations and "solvable" ideals.
-- 
-- See  Property_LinSolvRing  below,  (Manual `linr', 'gx').


class (CommutativeRing a, MulMonoid a) => LinSolvRing a  
  where
  baseLinSolvRing :: a -> Domains1 a -> (Domains1 a, LinSolvRingTerm a)
  gxBasis         :: [a] -> ([a], [[a]])
                    -- xs    gs   mt      

  moduloBasis :: String -> [a] -> a -> (a, [a])
  syzygyGens  :: String -> [a] -> [[a]]          

isGxRing :: LinSolvRingTerm a -> PropValue
isGxRing = lookupProp IsGxRing . linSolvRingProps 

------------------------------------------------------------------------
class (GCDRing a, LinSolvRing a) => EuclideanRing a  
  where
  baseEucRing :: a -> Domains1 a -> (Domains1 a, EucRingTerm a)

  eucNorm :: a -> Natural
  divRem  :: Char -> a -> a -> (a, a)
          --
          -- mode -> x -> y -> (quotient,remainder)
          -- mode = 'm'  means the Minimal-norm remainder, 
          --        'c'  means for each  b /= 0   x -> divRem 'c' x b
          --             is a canonical map for the residues modulo b

  -- The correctness of  eucNorm, divRem   depends on the property 
  -- values  Euclidean, DivRemCan, DivRemMin  - see below.


isEucRing, isCEucRing :: EucRingTerm a -> PropValue

isEucRing  = lookupProp Euclidean . eucRingProps
isCEucRing = lookupProp DivRemCan . eucRingProps

------------------------------------------------------------------------
class (EuclideanRing a, FactorizationRing a) => Field a 
                                             -- presumed: (IsField, Yes)

class Field a => RealField a             -- presumed: (IsRealField, Yes)

class (RealField a, OrderedRing a) => OrderedField a

------------------------------------------------------------------------
type ADomDom a = a -> Domains1 a -> Domains1 a

upRing              :: Ring              a => ADomDom a
upGCDRing           :: GCDRing           a => ADomDom a
upFactorizationRing :: FactorizationRing a => ADomDom a
upLinSolvRing       :: LinSolvRing       a => ADomDom a
upEucRing           :: EuclideanRing     a => ADomDom a
upField             :: Field             a => ADomDom a

upGCDLinSolvRing :: (GCDRing a, LinSolvRing a)             => ADomDom a
upEucFactrRing   :: (EuclideanRing a, FactorizationRing a) => ADomDom a
upFactrLinSolvRing :: (FactorizationRing a, LinSolvRing a) => ADomDom a

upRing a =  fst . baseRing a . fst . baseMulSemigroup a . upAddGroup a

upGCDRing           a = fst . baseGCDRing     a . upRing a
upFactorizationRing a = fst . baseFactrRing   a . upGCDRing a
upLinSolvRing       a = fst . baseLinSolvRing a . upRing a
upGCDLinSolvRing    a = fst . baseLinSolvRing a . upGCDRing a
upEucFactrRing      a = fst . baseFactrRing   a . upEucRing a
upFactrLinSolvRing  a = fst . baseLinSolvRing a . upFactorizationRing a
upEucRing a = fst. baseEucRing a . fst . baseLinSolvRing a . upGCDRing a
upField     = upEucFactrRing

------------------------------------------------------------------------
isFactorizOfPrime, isFactorizOfPrimary :: Factorization a -> PropValue

isFactorizOfPrime [(_, 1)] = Yes
isFactorizOfPrime (_: _)   = No
isFactorizOfPrime _        = Unknown

isFactorizOfPrimary [_]    = Yes
isFactorizOfPrimary (_: _) = No
isFactorizOfPrimary _      = Unknown

rankFromIdeal :: Ideal a -> InfUnn Natural
rankFromIdeal iI =  case  lookup IdealRank $ idealOpers iI
                    of
                    Just (IdealRank' v) -> v
                    _                   -> UnknownV
                    

isMaxIdeal, isPrimeIdeal, isPrimaryIdeal :: Ideal a -> PropValue

isMaxIdeal     = lookupProp IsMaxIdeal . idealProps
isPrimeIdeal   = lookupProp Prime      . idealProps
isPrimaryIdeal = lookupProp Primary    . idealProps


genFactorizationsFromIdeal :: Ideal a -> Maybe [Factorization a]
                             -- Extracts the factorization list from the
                             -- FIRST `GenFactorizations' construction

genFactorizationsFromIdeal iI = findFtCons $ idealConstrs iI
  where
  findFtCons []                           = Nothing
  findFtCons ((GenFactorizations fts): _) = Just fts
  findFtCons constrs                      = findFtCons $ tail constrs

------------------------------------------------------------------------
zeroIdeal :: Properties_Ideal -> Subring a -> Ideal a

-- Zero ideal in a Non-zero base ring.
-- iprops  contains some hints for the ideal properties. 

zeroIdeal givenProps rR =  Ideal {idealGens     = Just [],
                                  idealProps    = iProps,
                                  idealGenProps = [(IsGxBasis, Yes)],
                                  idealConstrs  = [],
                                  idealOpers    = opers}
  where
  opers    = [(IdealRank, IdealRank' $ Fin 0)] 
  propsR   = subringProps rR
  hasZD    = lookupProp HasZeroDiv    propsR
  primaryR = lookupProp IsPrimaryRing propsR

  [maxI, primeI, primaryI] = [lookupProp p givenProps | 
                                      p <- [IsMaxIdeal, Prime, Primary]]
  iProps = [(IsMaxIdeal, max'), (Prime, prime'), (Primary, primary')]
  max' = if maxI == Yes then 
                        error $ msg "(Maximal, Yes)  wrongly set.\n"
         else           No
  msg = 
       showString "zeroIdeal givenProperties rR,\ngivenProperties =  " .
       shows givenProps . showString "\n\n"

  prime' = case (primeI, hasZD) 
           of  
           (Yes, Yes) -> error $ msg 
                            "(Prime, Yes) contradicts  rR  properties\n"
           (No,  No ) -> error $ msg 
                              "(Prime, No) contradicts rR  properties\n"
           (Yes, _  ) -> Yes
           (No , _  ) -> No
           (_,   v  ) -> not3 v

  primary' = case (primaryI, primaryR) 
             of  
             (Yes, No ) -> error $ msg 
                            "(Primary, Yes) contradicts rR properties\n"
             (Yes, _  ) -> Yes
             (No,  Yes) -> error $ msg
                           "(Primary, Yes)  contradicts rR properties\n"
             (_,   v  ) -> v


------------------------------------------------------------------------
unityIdeal :: a -> Subring a -> Ideal a
unityIdeal    un   _ =               -- unity ideal in a given base ring

 Ideal {idealGens     = Just [un],
        idealProps    = props,
        idealGenProps = [(IsGxBasis, Yes)],
        idealConstrs  = [],
        idealOpers    = operations
       }
       where  
       operations = [(IdealRank, IdealRank' $ Fin 1)]
       props      = [(IsMaxIdeal, No), (Prime, No), (Primary, No)]
