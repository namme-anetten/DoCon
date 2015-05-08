------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------





module Matr0_   -- Some Matrix operations, 
                -- All needed from here is  reexported by  VecMatr.

( {- class -} MatrixLike(..),  Matrix(..),     -- from Ring0_
 MatrixSizes(..), -- class
 SquareMatrix(..),
 toSqMt, fromSqMt, isZeroMt, mtHead, matrHead, mtTail, constMt,
 rowMatrMul, matrMul, diagonalMt, scalarMt, mainMtDiag, isDiagMt, 
 isStaircaseMt, isLowTriangMt, vandermondeMt, resultantMt
 -- , instances for  Matrix and SquareMatrix:  
 --                             Read, Eq, MatrixLike, MatrixSizes.
)
where
import Data.List (transpose)
import DPrelude  (Length(..), -- class 
                                 Natural, mapmap, showsWithDom )
import Categs (Dom(..), Domains1)
import List_  (binOpList)
import SetGroup  
import Ring0_ (MatrixLike(..), -- class
               CommutativeRing(), Matrix(..))






------------------------------------------------------------------------
-- Recall:  a matrix  (Mt rs dm)  must contain a Non-empty list of
--          non-empty lists of the Same length.


data SquareMatrix a = SqMt [[a]] (Domains1 a)

-- In  SqMt rows dm  it is PRESUMED  (length xs)==(length rows) > 0  
-- for each  xs  from  rows

instance Eq a => Eq (SquareMatrix a) where 
                                     x == y =  mtRows x == mtRows y

instance Dom Matrix  where  dom (Mt _ d) = d
                            sample       = matrHead

instance Dom SquareMatrix  where  dom (SqMt _ d) = d
                                  sample         = mtHead . mtRows

instance MatrixLike SquareMatrix where  
                             mtRows (SqMt rs _)  = rs
                             transp (SqMt rs d)  = SqMt (transpose rs) d
                             mapMt f (SqMt rs d) = SqMt (mapmap f  rs) d

class MatrixSizes a where mtHeight :: a -> Natural
                          mtWidth  :: a -> Natural
                                      -- for [[a]], Matrix, SquareMatrix

instance MatrixSizes [[a]] where mtHeight = genLength 
                                 mtWidth []     = error "\nmtWidth []\n"
                                 mtWidth (r: _) = genLength r

instance MatrixLike m => MatrixSizes (m a) where 
                                           mtHeight = mtHeight . mtRows
                                           mtWidth  = mtWidth  . mtRows

toSqMt :: Matrix a -> SquareMatrix a
toSqMt (Mt rs dom) =  SqMt rs dom          -- CAUTION: rs must be square

fromSqMt :: SquareMatrix a -> Matrix a
fromSqMt (SqMt rs d) =  Mt rs d

mtHead :: [[a]] -> a 
mtHead ((x: _): _) = x
mtHead _           = error "\nmtHead mM:  empty mM.\n"

matrHead :: MatrixLike m => m a -> a
matrHead =  mtHead . mtRows

mtTail :: MatrixLike m => m a -> [[a]] 
mtTail mM =  case mtRows mM of 
                            _: rs -> rs
                            _     -> error "\nmtTail <emptyMatrix>.\n"

constMt :: MatrixLike m => m a -> a -> m a
constMt mM a =  mapMt (const a) mM 

------------------------------------------------------------------------
rowMatrMul :: CommutativeRing a => [a] -> [[a]] -> [a]

                 -- product of a Row by a Matrix.
                 -- Method:  x1*row1 +...+ xN*rowN,  where  row=[x1..xN]
rowMatrMul r rs =  
  (case 
       (r, rs)  
   of
   (x: xs, row: rows) -> rmm xs rows $ map (x *) row
   (_: _,  _        ) -> error $ msg msg'
   _                  -> error $ msg "\n"
  )
  where
  r1  = head r
  msg = showString "\nrowMatrMul row mM: \nnon-empty  row, mM  \
                   \required, and\n(length row) = (mtHeight mM).\n"

  msg' = showString "\n\nHere " $ showsWithDom 1 r1 "head row" "" "\n"

  rmm []      []          res = res
  rmm (x: xs) (row: rows) res =
                         rmm xs rows $ binOpList (+) res $ map (x *) row
  rmm _       _           _   = error $ msg msg'

------------------------------------------------------------------------
matrMul :: CommutativeRing a => Matrix a -> Matrix a -> Matrix a
                      -- product of matrices  (n x m),(m x k) -> (n x k)

matrMul (Mt rs1 d) (Mt rs2 _) =  Mt [rowMatrMul r rs2 | r <- rs1] d

isZeroMt :: AddSemigroup a => [[a]] -> Bool
isZeroMt rows@((a: _): _) =  case zero_m a of 
                                         Just z -> all (all (== z)) rows
                                         _      -> False
isZeroMt _ =  error "\nisZeroMt  for empty matrix.\n"

mainMtDiag :: [[a]] -> [a]         -- main diagonal = [m(i,i)| i<- [1..]
mainMtDiag rows = 
                 case rows  
                 of
                 []     -> []
                 []: _  -> error "\nmainMtDiag rows:  empty head row.\n"
                 r : rs -> (head r): (mainMtDiag $ map tail rs)

------------------------------------------------------------------------
isDiagMt :: AddGroup a => [[a]] -> Bool          -- "is diagonal matrix"
isDiagMt rows =
    case rows of
              (a: _): _ -> case  zero_m a  of  Just z -> d z rows
              _         -> error "\nisDiagMt  for empty pre-matrix.\n"
 where      
 d _ []          = True
 d _ [[_]]       = True
 d _ ([]:  rows) = all null rows
 d z (row: rows) = (all (== z) $ tail row     ) &&
                   (all (== z) $ map head rows) && (d z $ map tail rows)

------------------------------------------------------------------------
isStaircaseMt :: AddGroup a => [[a]] -> Bool
isStaircaseMt rows = 
         case rows 
         of
         (a: _): _ -> case zero_m a of Just z -> isst z rows 
         _         -> error "\nisStaircaseMt  for empty pre-matrix.n"
  where
  isst z (row: rs) = sm (genLength zeroes) nonzs rs
    where
    (zeroes, nonzs) = span (== z) row  

    sm _ _  []     = True  
    sm _ [] rs     = all (all (== z)) rs  
    sm l _  (r:rs) = (l1 > l) && (sm l1 nonzs1 rs)
                                        where
                                        (zs, nonzs1) = span (== z) r
                                        l1           = genLength zs

------------------------------------------------------------------------
isLowTriangMt :: AddGroup a => [[a]] -> Bool
isLowTriangMt rows  = 
         case rows  
         of
         (a:_): _ -> case zero_m a of Just z -> isT z rows
         _        -> error "\nisLowTriangMt  for empty pre-matrix.\n"
    where
    isT _ []               = True
    isT _ ([]:       _   ) = True
    isT z ((_: row): rows) = (all (== z) row) && (isT z $ map tail rows)

------------------------------------------------------------------------
diagonalMt :: a -> [a] -> [[a]]
           -- z    ds
-- Make the diagonal square pre-matrix from the given main diagonal 
-- elements  ds,  putting zero  z  to other positions.  COST =  O(n^2).

diagonalMt z ds =  diagRows ds
 where
 diagRows []      = []
 diagRows [d]     = [[d]]
 diagRows (d: ds) = (d: z: row): (z: x: row): [z: r | r <- rows]
                                        where
                                        ((x: row): rows) = diagRows ds

scalarMt :: [a] -> b -> b -> [[b]]
           -- xs   c    z
-- Make the scalar pre-matrix  n x n  from the given elements  c, z  and 
--      the list  xs  of length n,  xs  serves as a counter.
-- c  is put to the main diagonal,  z  is put to other positions.
-- COST =  O(n^2).

scalarMt xs c z =  diagonalMt z $ map (const c) xs

------------------------------------------------------------------------
vandermondeMt :: MulMonoid a => [a] -> [[a]]

  -- [a0..an] -> [[a0^n     .. an^n    ]
  --              [a0^(n-1) .. an^(n-1)] 
  --              ...
  --              [1        .. 1       ] 
  --             ]

vandermondeMt  []       = error "\nvandermondeMt [].\n"
vandermondeMt  xs@(x:_) = 
  case unity_m x 
  of
  Just u -> reverse $ vd xs $ map (const u) xs
         where
         vd []           _   = []
         vd (_: counter) row = row: (vd counter $ zipWith mul row xs)

  Nothing -> error $ showString "\nvandermondeMt (x: _)," $
                     showsWithDom 1 x "x" ""  "\n(unity x)  failed.\n"

------------------------------------------------------------------------
resultantMt :: AddGroup a => [a] -> [a] -> [[a]]

  -- For the coefficient lists  xs = x:_,  ys = y:_   of dense 
  --   polynomials f = x*t^n+.., g = y*t^m +.. from a[t],  
  --   n = deg f, m = deg g,  n,m > 0,   x,y  non-zero,  
  -- build the resultant matrix  M  over `a' for f,g.
  -- (so  det M = resultant f g).
  -- Example:
  -- [a3,0,a1,0] -> [b2,b1,b0] -> [[a3, 0 , a1, 0 , 0 ]
  --                               [0 , a3, 0 , a1, 0 ]
  --                               [b2, b1, b0, 0 , 0 ]
  --                               [0 , b2, b1, b0, 0 ]
  --                               [0 , 0 , b2, b1, b0]
  --                              ]
  -- Method.
  -- For  n = deg f = |xs|-1,  m = deg g = |ys|-1,
  -- zeroes prepend to  xs, ys  to make  xs0, ys0   both of length
  -- n+m.  M = (xs0 shifted m times)++(ys0 shifted n times),
  -- shifting means the round left shift.

resultantMt xs ys =  
  (case (xs, ys)  
   of
   (x: _: _, _: _: _) -> rsm (zeroS x) xs (tail xs) ys $ tail ys
   (x:_,     _      ) -> error (msg ++ (msg1 x))
   _                  -> error msg
  )
  where
  msg = "\nresultantMt xs ys:  length xs, length ys > 1 required.\n"
  msg1 x = showString "\n\nHere " $ showsWithDom 1 x "head xs" "" "\n"

  rsm z xs xs' ys ys' = (rm xs ys') ++ (rm ys xs')
    where
    rm xs [_]          = [xs]           -- m = 1, example: [[a3,0,a1,0]]
    rm xs (_: counter) = (row ++ [z]): (map (z :) (row: rows))
                                            where
                                            row: rows = rm xs counter








{- reserve  ***************************************************
instance (Convertible a b, AddSemigroup b)=> Convertible a (Matrix b)
  where
  -- c -> mt --> scalar matrix with c on diagonal
  --             - if mt is square and semigroup of b has zero
  cvm a m = if  (matrHeight m)/=(matrWidth m)  then  Nothing
            else        fmap fromSqMt (cvm a (toSqMt m))
instance Convertible a b => Convertible (Matrix a) (Matrix b)
  where
  cvm  m@(Mt rs _) m'@(Mt rs' doms') =
    if (matrHeight m)/=(matrHeight m') ||
      (matrWidth  m)/=(matrWidth  m')     then Nothing
    else
      case  (rs,rs')
      of ((a:_):_, (b:_):_) ->
          if isJust (cvm a b)  then
                            Just $ Mt (mapmap (\x->cv x b) rs) doms'
          else           Nothing
        _       ->  error "cvm (Mt..) (Mt..):  incorrect matrix\n"

instance (Convertible a b, AddSemigroup b) => 
                                  Convertible a (SquareMatrix b) where
  -- c  converts to scalar matrix with c on diagonal
  cvm a (SqMt rows doms) = case  rows  of
    ((b:_):_) ->  (case  (zero_m b, cvm a b) of
             (Just z,Just c) -> Just (SqMt (scalarMt rows c z) doms)
             _               -> Nothing
           )
    _         -> error "cvm _ (SqMt..):  empty matrix\n" 
***********************************************************
-}










