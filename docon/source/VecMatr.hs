------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,   2012
------------------------------------------------------------------------
------------------------------------------------------------------------




module VecMatr
            -- Vector, Matrix  operations and their  category instances.
            -- This head module implements the  matrix instances  and 
            -- reexports other needed items from other modules.
(
 -- Vector(..),                   from Categs
 vecRepr,  {- Eq Vector, -}    -- from Categs
 {- class -} MatrixLike(..),   Matrix(..),                -- from Ring0_

 -- from Vec0_
 allMaybesVec, vecSize, vecHead, vecTail, constVec, scalProduct,
 -- instance Functor

 -- from Vec1_  
 vecBaseSet, vecBaseAddSemigroup, vecBaseAddGroup, 
 vecBaseMulSemigroup, vecBaseMulGroup, vecBaseRing,

 module Vec_,    
 -- instances for Vector:
 -- Show, DShow, Set, OrderedSet, AddSemigroup, AddMonoid,
 -- OrderedAddSemigroup, OrderedAddMonoid, AddGroup, OrderedAddGroup,
 -- MulSemigroup, OrderedMulSemigroup, MulMonoid, MulGroup, Ring,
 -- CommutativeRing, OrderedRing, Num, Fractional,
 
 -- from Matr0_:
 {- class -} MatrixSizes(..),  SquareMatrix(..),  
 toSqMt, fromSqMt, mtHead, matrHead, isZeroMt, mtTail, constMt, 
 rowMatrMul, diagonalMt, scalarMt, mainMtDiag, isDiagMt, isStaircaseMt, 
 isLowTriangMt, vandermondeMt, resultantMt,

 -- from Matr1_:
 matrBaseSet, matrBaseAddSemigroup, matrBaseAddGroup, sqMatrBaseSet, 
 sqMatrBaseAddSemigroup, sqMatrBaseAddGroup, sqMatrBaseMulSemigroup, 
 sqMatrBaseRing
)
where
import Data.Maybe (fromJust)
import Data.List  (intersperse)

import DPrelude (DShow(..), -- class 
                 ShowOptions(..),  
                 compose, addToShowOptions, showsn, showsWithDom
                )
import Categs (Dom(..), vecRepr)
import SetGroup  
import Ring0_    
import Vec0_
import Vec1_
import Vec_
import Matr0_
import Matr1_



------------------------------------------------------------------------
instance DShow a => Show  (Matrix a) where showsPrec _ = showsn 0 
instance DShow a => DShow (Matrix a) 
  where  
  dShows opt mt = showString header . 
                  (showRows $ map (dShows opt') (mtRows mt)) . 
                  showString footer
              where
              showRows = compose . intersperse (showString rowSep) 
              opt'     = addToShowOptions (-1) opt
              verbty   = verbosity opt
              rowSep   = if verbty < 3 then ",\n    " else "\n,\n"
              (header, footer) = if verbty < 2 then ("(Mt [", "])")
                                 else
                                 case verbty of 2 -> ("(Mt [",   "\n])")
                                                _ -> ("(Mt [\n", "\n])")

instance DShow a => Show  (SquareMatrix a) where showsPrec _ = showsn 0
instance DShow a => DShow (SquareMatrix a) where 
                                      dShows opt = dShows opt . fromSqMt

instance Set a => Set (Matrix a) 
  where   
  baseSet   = matrBaseSet
  compare_m = compareTrivially

  showsDomOf verb mM = 
    case (mtHeight mM, mtWidth mM) 
    of 
    (0, _) -> error "\nshowsDomOf verb (Mt []).\n"
    (n, 0) -> error $ showString "\nshowsDomOf verb mM:   " $ 
                      shows n " x  0  <matrix>.\n"

    (n, m) -> showString "(L " . shows n . showChar ' ' . shows m . 
              showChar ' ' . showsDomOf (pred verb) (matrHead mM) . 
              showChar ')'

  fromExpr mM e = case (mtRows mM, dom mM)
                  of
                  ([],   _) -> ([], "empty sample matrix")
                  (rows, d) -> case fromExpr rows e  
                               of
                               ([rs], "" ) -> ([Mt rs d], "" )
                               (_   , msg) -> ([],        msg)


instance OrderedSet a => Ord (Matrix a) where
                                      compare x = fromJust . compare_m x

instance OrderedSet a => OrderedSet (Matrix a)

instance Set a => Set (SquareMatrix a)  
  where   
  baseSet   = sqMatrBaseSet
  compare_m = compareTrivially
  showsDomOf verb mM = 
         case mtHeight mM 
         of
         0 -> error "\nshowsDomOf (SqMt []).\n"
         n -> showString "L " . shows n . showChar ' ' . 
              showsDomOf (pred verb) (mtHead $ mtRows mM) . showChar ')'
          
  fromExpr (SqMt rows d) e =  case  fromExpr rows e  of
                                       ([rs], "" ) -> ([SqMt rs d], "" )
                                       (_,    msg) -> ([],          msg)


instance OrderedSet a => Ord (SquareMatrix a) where
                                      compare x = fromJust . compare_m x 

instance OrderedSet a => OrderedSet (SquareMatrix a)


------------------------------------------------------------------------
-- The additive (semi)group  for matrices is isomorphic to the  
-- additive (semi)group of the vectors of size n*m.

instance AddGroup a => AddSemigroup (Matrix a)  
  where 
  baseAddSemigroup = matrBaseAddSemigroup

  add (Mt rs dm) (Mt rs' _) = Mt (zipWith (zipWith add) rs rs') dm

  zero_m  m@(Mt rs _) = 
                      case rs 
                      of
                      (e: _): _ -> Just $ mapMt (const z) m
                                                      where  z = zeroS e
                      _       -> 
                        error "\nzero_m (Mt rows dom):  empty matrix.\n"

  neg_m       = Just . mapMt neg
  times_m m n = Just $ mapMt (\ x -> times x n) m


------------------------------------------------------------------------
instance AddGroup a => AddSemigroup (SquareMatrix a)  
  where 
  baseAddSemigroup = sqMatrBaseAddSemigroup 

  add (SqMt rs d) (SqMt rs' _) = toSqMt $ add (Mt rs d) (Mt rs' d)

  zero_m  m@(SqMt rs _) = 
                     case rs 
                     of
                     (e: _): _ -> Just $ mapMt (const z) m
                                                      where  z = zeroS e
                     _       -> 
                      error "\nzero_m (SqMt rows dom):  empty matrix.\n"

  neg_m       = Just . mapMt neg
  times_m m n = Just $ mapMt (\ x -> times x n) m

------------------------------------------------------------------------
instance OrderedAddGroup a => OrderedAddSemigroup (Matrix a)  
instance AddGroup        a => AddMonoid           (Matrix a)  
instance OrderedAddGroup a => OrderedAddMonoid    (Matrix a)  
instance OrderedAddGroup a => OrderedAddSemigroup (SquareMatrix a)  
instance AddGroup        a => AddMonoid           (SquareMatrix a)  
instance OrderedAddGroup a => OrderedAddMonoid    (SquareMatrix a)  

instance AddGroup a => AddGroup (Matrix a)  where
                                         baseAddGroup = matrBaseAddGroup

instance AddGroup a => AddGroup (SquareMatrix a)  
  where
  baseAddGroup = sqMatrBaseAddGroup 

instance OrderedAddGroup a => OrderedAddGroup (Matrix a)
instance OrderedAddGroup a => OrderedAddGroup (SquareMatrix a)

------------------------------------------------------------------------
instance CommutativeRing a => MulSemigroup (SquareMatrix a)  
  where
  baseMulSemigroup = sqMatrBaseMulSemigroup

  mul (SqMt rs d) (SqMt rs' _) =  toSqMt $ matrMul (Mt rs d) (Mt rs' d)

  unity_m (SqMt rs d) = 
           case rs 
           of
           (e: _): _ -> Just $ SqMt (scalarMt rs u z) d
                                            where  
                                            (z, u) = (zeroS e, unity e)  
           _ -> error "\nunity_m (SqMt rows dom):  empty matrix.\n"

  divide_m _ _ = 
       error $ concat ["\ndivide_m (SqMt _ _) (SqMt _ _):   ",
                       "is not defined for square matrices, so far.\n",
                       "For Euclidean domain  e,  use  ",
                       "inverseMatr_euc (m :: Matrix e) ...\n"]

  -- ?             
  -- inv_m m =  case inverseMatr(_euc?) m  of [] -> Nothing
  --                                          im -> Just im
  -- divide_m  t u =   ... toDiagMatr_ ...

  divide_m2 _ _ = 
       error $ concat ["\ndivide_m2 (SqMt _ _) (SqMt _ _):   ",
                       "is not defined for square matrices, so far.\n",
                       "For Euclidean domain  e,  use  ",
                       "inverseMatr_euc (m :: Matrix e) ...\n"]
  root _ _ = 
       error $ concat ["\nroot n (SqMt _ _):   ",
                       "is not defined for square matrices, so far.\n"]
   

------------------------------------------------------------------------
instance (CommutativeRing a, MulMonoid a) => MulMonoid (SquareMatrix a)

instance CommutativeRing a => Num (Matrix a)  
  where
  negate = mapMt neg
  (+)    = add
  (*)    = matrMul 
  m-m'   = add m (neg m')
  signum _ = error "\nsignum (Mt _)  is not defined for (Matrix _).\n" 
  abs    _ = error "\nabs (Mt _)  is not defined for (Matrix _).\n" 
  fromInteger _ = 
                 error "\nfromInteger:  use  fromi, fromi_m  instead.\n"

instance CommutativeRing a => Num (SquareMatrix a)  
  where
  negate = mapMt neg
  (+)    = add 
  (-)    = sub 
  (*)    = mul 
  signum _ = error 
             "\nsignum (SqMt _)  is not defined for (SquareMatrix _).\n"
  abs _ = error "\nabs (SqMt _)  is not defined for (SquareMatrix _).\n" 
  fromInteger _ = 
                 error "\nfromInteger:  use  fromi, fromi_m  instead.\n" 


instance CommutativeRing a => Fractional (Matrix a)      
  where
  fromRational _ = error $ concat 
                   ["\nfromRational (Mt _):  \n",
                    "Fractional  instance is dummy for (Matrix _).\n",
                    "For Euclidean domain  e,  use  ",
                    "inverseMatr_euc (m :: Matrix e) ...\n"]
  recip _ = error $ concat 
                   ["\nrecip (Mt _):  \n",
                    "Fractional  instance is dummy for (Matrix _).\n",
                    "For Euclidean domain  e,  use  ",
                    "inverseMatr_euc (m :: Matrix e) ...\n"]

instance CommutativeRing a => Fractional (SquareMatrix a) 
  where
  fromRational _ = error $ concat 
                   ["\nfromRational (SqMt _):  \n",
                    "Fractional  instance is dummy for (SquareMatrix _).\n",
                    "For an Euclidean domain  e,  use  ",
                    "inverseMatr_euc (m :: Matrix e) ...\n"]
  recip _ = error $ concat 
                   ["\nrecip (SqMt _):  \n",
                    "Fractional  instance is dummy for (SquareMatrix _).\n",
                    "For an Euclidean domain  e,  use  ",
                    "inverseMatr_euc (m :: Matrix e) ...\n"]


------------------------------------------------------------------------
instance CommutativeRing a => Ring (SquareMatrix a) 
  where
  baseRing = sqMatrBaseRing

  fromi_m mt n =  
    case  
        (mtRows mt, unity_m mt)
    of
    ((e: _): _, Just uM) -> case fromi_m e n
                            of
                            Just c -> Just $ mapMt (mul c) uM
    ((e: _): _, _      ) -> 
                   error $ msg $ showsWithDom 1 e "mtHead mM" "R" $
                                 "\nunity not found in  R.\n"
    (_,         Just uM) -> 
                    error $ msg $ ("R =  "++) $ 
                    showsDomOf 1 (mtHead $ mtRows uM) "\n\nEmpty  mM.\n"
    where  
    msg = showString "\nfromi_m mM " . shows n . 
          showString ",\nwhere mM = sampleSquareMatrix\
                     \  over R  has size  " .
          shows (mtHeight mt) . showString "\n"
