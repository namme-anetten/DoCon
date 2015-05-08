------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------





module Vec_  -- Category  instances for the  Vector domain over `a'.
             -- All needed from here is  reexported by  VecMatr.

(Vector(..)   -- from Categs

 -- , instances for Vector:
 -- Show, DShow, Set, OrderedSet, AddSemigroup, AddMonoid,
 -- OrderedAddSemigroup, OrderedAddMonoid, AddGroup, 
 -- OrderedAddGroup, MulSemigroup, OrderedMulSemigroup, 
 -- MulMonoid, MulGroup, Num, Fractional, Ring, CommutativeRing,
 -- OrderedRing
)
where
import System.Random (Random(..))   -- non-standard, non-GHC
                                            
import Data.Maybe  (fromJust, catMaybes)

import DPrelude (DShow(..), showsn, showsWithDom)
import Categs   (Vector(..), vecRepr)
import SetGroup 
import Ring0_
import Vec0_
import Vec1_ (vecBaseSet,      vecBaseAddSemigroup,
              vecBaseAddGroup, vecBaseMulSemigroup, 
              vecBaseMulGroup, vecBaseRing)




------------------------------------------------------------------------
instance DShow a => Show (Vector a) where  showsPrec _ = showsn 0
instance DShow a => DShow (Vector a)  
  where   
  dShows opt v = showString "(Vec " . dShows opt (vecRepr v) . 
                 showChar ')'

instance Random a => Random (Vector a)
  where
  randomR (vl, vh) g = (Vec $ reverse xs, g')
          where
          (xs, g') = foldl rnd ([], g) $ zip (vecRepr vl) (vecRepr vh)

          rnd (xs, g) (l, h) = (x: xs, g')  where  
                                            (x, g') = randomR (l, h) g 
  random _ = error "random:  use randomR\n"                                
       
------------------------------------------------------------------------
instance Set a => Set (Vector a)  
  where   
  baseSet = vecBaseSet

  showsDomOf verb v = 
                 case vecRepr v 
                 of
                 []   -> showString "{Vec 0 ?}"
                 a: _ -> showString "{Vec " . showsDomOf (pred verb) a . 
                         showChar '}'

  fromExpr v e = case  fromExpr (vecRepr v) e  of
                                          ([ys], "" ) -> ([Vec ys], "" )
                                          (_   , msg) -> ([]      , msg)

  compare_m u v = cmpLex (vecRepr u) (vecRepr v)
                           -- Looks like a partial ordering. Be careful!
    where
    cmpLex [x]     [y]     = compare_m x y
    cmpLex (x: xs) (y: ys) = case compare_m x y of
                                               Nothing -> Nothing
                                               Just EQ -> cmpLex xs ys
                                               v       -> v
    cmpLex _      _        =  
       error $ showString "\ncompare_m: u v   for  u,v <- Vector X\
                         \  of sizes\n" $
               shows (vecSize u) $ showString ", " $ shows (vecSize v) $
               msg "\n:\nu, v  must be of the same non-zero size.\n"

    msg = case map vecRepr [u, v] of
                                 [_: _, _   ] -> showsWithDom 1 u "u" ""
                                 [_,    _: _] -> showsWithDom 1 v "v" ""
                                 _            -> id


------------------------------------------------------------------------
instance OrderedSet a => Ord (Vector a) where
                                      compare u = fromJust . compare_m u 

instance OrderedSet a => OrderedSet (Vector a)

                             -- Additive semigroup  A+A+...+A  (n-times)
instance AddGroup a => AddSemigroup (Vector a) 
  where 
  baseAddSemigroup      = vecBaseAddSemigroup
  add (Vec xs) (Vec ys) = Vec $ zipWith add xs ys

  zero_m v =  case zero_m $ vecHead v of  Just z -> Just $ constVec v z

  neg_m       = Just . fmap neg
  times_m v n = Just $ fmap (\ x -> times x n) v

------------------------------------------------------------------------
instance AddGroup        a => AddMonoid           (Vector a)  
instance OrderedAddGroup a => OrderedAddSemigroup (Vector a)
instance OrderedAddGroup a => OrderedAddMonoid    (Vector a)

instance AddGroup a => AddGroup (Vector a)  where  
                                          baseAddGroup = vecBaseAddGroup

instance OrderedAddGroup a => OrderedAddGroup (Vector a)

instance MulSemigroup a => MulSemigroup (Vector a)  
  where
  baseMulSemigroup      = vecBaseMulSemigroup
  mul (Vec xs) (Vec ys) = Vec $ zipWith mul xs ys
                               -- as in the direct product of semigroups

  unity_m v = fmap (constVec v) $ unity_m $ vecHead v

  inv_m = allMaybesVec . map inv_m . vecRepr

  divide_m (Vec xs) (Vec ys) = allMaybesVec $ zipWith divide_m xs ys

  divide_m2 _ _ = error ("\ndivide_m2 (Vec _) (Vec _):  " ++
                         "is not defined for vectors, so far.\n"
                        )
  power_m v n = allMaybesVec [power_m x n | x <- vecRepr v]

  root n v = 
            let rs = map (root n) $ vecRepr v  
            in
            case (any (== Just Nothing) rs, any (== Nothing) rs)
            of
            (True, _   ) -> Just Nothing
            (_,    True) -> Nothing
            _            -> Just $ Just $ Vec $ catMaybes $ catMaybes rs

------------------------------------------------------------------------
instance OrderedMulSemigroup a => OrderedMulSemigroup (Vector a)
instance MulMonoid           a => MulMonoid           (Vector a)
instance MulGroup            a => MulGroup (Vector a)  
                                     where  
                                     baseMulGroup = vecBaseMulGroup

instance Ring a => Num (Vector a)  
  where 
  negate   = fmap neg
  (+)      = add
  u-v      = add u $ fmap neg v
  (*)      = mul
  signum _ = error "\nsignum (Vec _):  is not defined for Vector.\n"
  abs    _ = error "\nabs (Vec _):  is not defined for Vector.\n"
  fromInteger _ = 
                 error "\nfromInteger:  use  fromi, fromi_m  instead.\n"

instance Ring a => Fractional (Vector a)  
  where 
  (/)            = divide         
  fromRational _ = 
       error "\nfromRational:  instead use  fromi  combined with (/).\n"

------------------------------------------------------------------------
instance Ring a => Ring (Vector a)       -- R x R x...x R   for a ring R
  where
  baseRing    = vecBaseRing
  fromi_m v n = fmap (constVec v) $ fromi_m (vecHead v) n 

instance CommutativeRing a => CommutativeRing (Vector a) 
instance OrderedRing     a => OrderedRing     (Vector a)     
