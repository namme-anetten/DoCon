------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.12
--
--  Copyright  Serge Mechveliani,    2012
------------------------------------------------------------------------
------------------------------------------------------------------------





module Permut 

  -- Permutation group. Just some tools.
  -- This implementation may have rather high cost order for the 
  -- permutations from S(n) of large n.
  -- In future, we may add the implementation based on the binary
  -- trees.

  (Permutation(..), EPermut, toEPermut, fromEPermut, permutRepr,
   isPermut, permutSign, isEvenPermut, applyPermut, applyTransp,
   applyTranspSeq, invEPermut, addEPermut, ePermutCycles, 
   permutECycles, permutCycles, transpsOfNeighb, allPermuts, 
   nextPermut, test_allPermuts, gensToSemigroupList
   -- , instances for  Permutation:
   -- Length, IsSingleton, Eq, Show, DShow, Ord, Num, Set, MulSemigroup,
   -- MulMonoid, MulGroup
  )

where
import qualified Data.Map as Map (lookup, insert)

import Data.Maybe (fromJust)
import Data.List  (genericSplitAt, nub, union)

import DPrelude   
       (Length(..), IsSingleton(..), DShow(..), -- classes
        PropValue(..), InfUnn(..),  toZ, factorial, mapmap, boolToPropV,
        compBy, lexListComp, mergeBy, sort, sortBy, isOrderedBy, sortE,
                                                                 showsn)
import Categs    
       (CategoryName(..), Domain1(..), OSet(..), Property_OSet(..), 
        Subsemigroup(..), Property_Subsemigroup(..), Subgroup(..), 
        Property_Subgroup(..), AddOrMul(..)
       )
import SetGroup (Set(..), MulSemigroup(..), MulMonoid(), MulGroup(..), 
                                                         unity, inv)





------------------------------------------------------------------------
newtype Permutation = Pm [Integer]  deriving (Eq, Read)
type    EPermut     = [(Integer, Integer)] 

-- In  Pm xs   xs  must not contain repetitions.
-- EPermut     is a Permutation whose list  xs  is zipped with  xs
--             sorted increasingly.

toEPermut :: Permutation -> EPermut
toEPermut (Pm xs) =  zip (sort xs) xs

fromEPermut :: EPermut -> Permutation 
fromEPermut = Pm . map snd

permutRepr :: Permutation -> [Integer]
permutRepr (Pm xs) =  xs

isPermut :: Permutation -> Bool
isPermut    (Pm xs)     =  (nub xs) == xs

permutSign :: Permutation -> Char                 -- '+'|'-'
permutSign =  snd . sortE compare . permutRepr

isEvenPermut :: Permutation -> Bool
isEvenPermut = (== '+') . permutSign


instance Length Permutation where  genLength = genLength . permutRepr
instance IsSingleton Permutation where  
                                 isSingleton = isSingleton . permutRepr

instance Show   Permutation where showsPrec _ = showsn 0
instance DShow  Permutation 
  where
  dShows _ (Pm js) =  showString "(Pm " . shows js . showChar ')'

instance Ord Permutation  
  where
  compare p = lexListComp compare (permutRepr p) . permutRepr 

applyPermut :: Ord a => [Integer] -> [a] -> [a]
applyPermut ks =  map snd . sortBy (compBy fst) . zip ks
  --
  -- example:  [2,3,4,1] -> "abbc" -> "cabb" 

------------------------------------------------------------------------
applyTransp :: DShow a => (Integer, Integer) -> [a] -> [a]      
  
-- Transpose the elements No i and j in list.  head xs  has No 1.
-- Required: 1 <= i <= j <= length xs.
  
applyTransp (i, j) xs =

 (case (compare i j, i < 1)
  of
  (EQ, _   ) -> xs
  (GT, _   ) -> error $ msg msgij
  (_ , True) -> error $ msg msgij
  _          ->
            case genericSplitAt (pred i) xs  
            of
            (_,  []    ) -> error $ msg msgl
            (ys, xi: zs) -> case genericSplitAt (j - i - 1) zs  
                            of
                            (us, xj: vs) -> ys ++ (xj: (us ++ (xi: vs)))
                            _            -> error $ msg msgl
 )
 where
 msg = showString "\napplyTransp  (i, j)=" . shows (i, j) . 
       showString "(xs = " . showsn 1 xs . showString ")\n:\n" 
 msgij = "\n1 <= i <= j  required.\n"
 msgl  = "\nj > length xs.\n"

------------------------------------------------------------------------
applyTranspSeq :: 
             (Ord a, DShow a, DShow b) => (a, a) -> [(a, b)] -> [(a, b)]
                                        -- i  j
-- Transpose the entities of indices  i <= j  in the sequence.
-- A sequence is a list of pairs  (k,x)  ordered increasingly by the 
-- index  k <- `a'.  Skipped index means a "zero" component.
-- Example:  for  ps = [(2,'2'),  (4,'4'),  (6,'6'),  (8,'8')],
-- 
--   applyTranspSeq (4,4) ps == applyTranspSeq (3,7) ps == ps,
--   map (flip applyTranspSeq ps) [(4,8),(4,7),(4,9)] ps 
--        ==
--        [(2,'2'),   (4,'8'),    (6,'6'),        (8,'4')]
--        [(2,'2'),               (6,'6'),(7,'4'),(8,'8')]
--        [(2,'2'),               (6,'6'),        (8,'8'),(9,'4')]
 
applyTranspSeq (i, j) ps = 

  case compare i j  
  of
  EQ -> ps
  GT -> error $ concat ["\napplyTranspSeq  (i, j)=", showsn 0 (i, j)
                        "\n ", showsn 1 ps "\n:\ni > j.\n"]
  _  -> tp ps
    where
    tp []           = []
    tp ((k, x): ps) = 
      (case 
           compare k i
       of
       LT -> (k, x): (tp ps)
       EQ -> tp1 $ span ((< j) . fst) ps           -- first entity found
       _  -> tp0 $ span ((< j) . fst) ((k, x): ps)  -- ..    skipped
      )
      where
      tp1 (_,   []          ) = ps ++ [(j, x)]   
      tp1 (ps', (l, y): ps'') = 
                       if  l == j  then  (i, y): (ps' ++ ((j, x): ps''))
                       else              ps' ++ ((j, x): (l,y): ps'')

      tp0 (_,   []          ) = (k, x): ps   -- both not found
      tp0 (ps', (l, y): ps'') = if l == j then  (i, y): (ps' ++ ps'')
                                else            (k, x): ps

------------------------------------------------------------------------
transpsOfNeighb :: [a] -> [[a]]

-- Transpositions of neighbour elements in xs = [x1..xn]  presents 
-- certain small generator list for S(n).
-- For  xs = [x],  the result is put [[x]].
-- For  Ord a,  x1 < x2 .. < xn,  the result really represents the 
-- transposition of neighbours.
-- Otherwise, it still gives the generator list of cardinality n-1
-- (for n > 1).

transpsOfNeighb [x] = [[x]]
transpsOfNeighb xs  = nbts xs
                where
                nbts [_]        = []
                nbts (x: y: xs) = (y: x: xs): (map (x :) $ nbts (y: xs))

------------------------------------------------------------------------
nextPermut :: [Integer] -> Maybe [Integer]
               -- Next permutation in the  reverse-lexicographic  order.
               -- The idea of the algorithm suggested by  S.M.Abramov.
nextPermut xs =
  (case
       spanMonotoneous xs
   of
   (_,    []   ) -> Nothing                      -- ordered increasingly
   (incr, j: js) -> 
        Just $ concat [reverse greaters, [j], reverse smallers, [i], js]
                               where
                               (smallers, i: greaters) = span (< j) incr
     -- [] /= incr  is ordered increasingly, and (last incr) > j.
     -- Hence  (incr++[j])  has the next permutation  nx  at the
     -- set j:incr,  and now  next(xs)  is built from  nx  and js
  )
  where
  spanMonotoneous (x: y: xs) = if x >= y then ([x],   y: xs)
                               else           (x: ys, zs   )
                                      where 
                                      (ys, zs) = spanMonotoneous (y: xs)
  spanMonotoneous xs         = (xs, [])

  -- why   reverse (i: (smallers ++ (j: greaters)))  is not faster ?
 
------------------------------------------------------------------------
instance Set Permutation 
  where
  compare_m  p = Just . compare p
  showsDomOf _ (Pm js) =  showString "S(" . shows (genLength js) . 
                          showChar ')'
                              -- on input, permutation looks like a list
  fromExpr (Pm xs) e = 
    case  
        fromExpr xs e  
    of
    ([ys], "") -> ([Pm ys], "")
    _          ->
        ([], concat ["(fromExpr ", shows (Pm xs) " ", showsn 1 e ")\n"])
 
  baseSet p dm = 
    case (Map.lookup Set dm, permutRepr p)  
    of
    (Just (D1Set s), _ ) -> (dm, s)
    (_             , []) -> error "baseSet (Pm []) currentDom\n"
    (_             , xs) -> (Map.insert Set (D1Set s) dm, s)
      where
      s = OSet {osetSample  = Pm xs,
                membership  = belongs,
                osetCard    = Fin $ factorial n,
                osetPointed = Just $ Just $ Pm xs,
                osetList    = Just $ allPermuts mxs,
                osetBounds  = (Just$ Just minp, Just$ Just maxp,
                               Just$ Just minp, Just$ Just maxp
                              ),
                osetProps = props, osetConstrs = [],  osetOpers = []
               }
      n     = genLength xs
      props = [(Finite,       Yes), (IsBaseSet,      Yes),
               (FullType,     No ), (OrderIsTrivial, No ),
               (OrderIsTotal, Yes), (OrderIsNoether, Yes),
               (OrderIsArtin, Yes)
              ]
      minp@(Pm mxs)     = Pm $ reverse $ sort xs
      maxp              = Pm $ reverse $ permutRepr minp
      belongs _ (Pm ys) = (Pm $ sort ys) == minp

------------------------------------------------------------------------
invEPermut :: EPermut -> EPermut                            -- inversion
invEPermut =  map (\ (x, y) -> (y, x)) . sortBy (compBy snd)

addEPermut :: EPermut -> EPermut -> EPermut 
                                -- compose permutations on disjoint sets
addEPermut p = mergeBy (compBy fst) p

------------------------------------------------------------------------
instance MulSemigroup Permutation
  where
  unity_m = Just . Pm . sort . permutRepr
  inv_m   = Just . fromEPermut . invEPermut . toEPermut

       -- mul p q = p*q  <--> \x-> p(q(x)).   Required:  set(p) = set(q)
       --
  mul p q = Pm $ map fst $ sortBy (compBy snd) $ 
                 zip (permutRepr p) $ permutRepr $ fromJust $ inv_m q 

  divide_m p = Just . mul p . inv

  divide_m2 _ = error "\ndivide_m2  for Permutation:  use  divide_m.\n" 
  root _ _    = error 
                "\nroot _  for Permutation is not defined, so far.\n"

  baseMulSemigroup p dm =
    case 
        (Map.lookup MulSemigroup dm, permutRepr p)  
    of
    (Just (D1Smg s), _ ) -> (dm, s)
    (_,              []) -> error "\nbaseMulSemigroup (Pm []) dom'.\n"
    (_,              xs) -> (Map.insert MulSemigroup (D1Smg s) dm, s)
      where
      s = Subsemigroup 
          {subsmgType    = Mul,     subsmgUnity = Just $ Just$ unity p,
           subsmgGens    = Just gs, subsmgProps = props,
           subsmgConstrs = [],      subsmgOpers = []
          }
      gs    = map Pm (transpsOfNeighb xs)
      props = [(Commutative,           less3  ),
               (IsGroup,               Yes    ),
               (IsMaxSubsemigroup,     No     ),
               (IsCyclicSemigroup,     less3  ),
               (IsOrderedSubsemigroup, Unknown)
              ]
      less3 = boolToPropV (genLength xs < 3)


------------------------------------------------------------------------
instance MulMonoid Permutation
instance MulGroup  Permutation
  where
  baseMulGroup p dm = 
   case 
       (Map.lookup MulGroup dm, permutRepr p) 
   of
   (Just (D1Group g), _ ) -> (dm, g)
   (_               , []) -> error "\nbaseMulGroup (Pm []) dom'.\n"
   (_               , xs) -> (Map.insert MulGroup (D1Group g) dm, g)
      where
      g = Subgroup {subgrType    = Mul,
                    subgrGens    = Just gs,
                    subgrCanonic = Just $ const $ unity p,
                    subgrProps   = props, 
                    subgrConstrs = [], 
                    subgrOpers   = []            
                   }
      gs    = map Pm $ transpsOfNeighb xs
      props = [(IsCyclicGroup, boolToPropV (n < 3)), 
               (IsPrimeGroup,  No), -- because A(n) is a normal subgroup
               (IsNormalSubgroup,  Yes),
               (IsMaxSubgroup,     No),
               (IsOrderedSubgroup, Unknown)
              ]
      n = genLength xs


------------------------------------------------------------------------
instance Num Permutation
  where
  (*) = mul

  -- (+) means composing permutations on disjoint sets
  --
  p + q = fromEPermut $ addEPermut (toEPermut p) $ toEPermut q

  signum _ = error "\nsignum  is senseless for Permutation.\n"
  abs    _ = error "\nabs  is senseless for Permutation.\n"
  fromInteger _ = 
              error "\nfromInteger  to Permutation:  it is senseless.\n"
  negate _ =  error "\nnegate <permutation>:  is not defined.\n"

------------------------------------------------------------------------
ePermutCycles :: EPermut -> [EPermut]
  
-- decompose  s  to cyclic permutations [c(1)..c(r)]:  
-- s = c(1) +..+ c(r),   length c(1) >= .. >= length c(r).

ePermutCycles p =  sortBy cmp $ cycs p
  where
  cmp c c' = compare (genLength c') $ genLength c

  cycs []           = []
  cycs ((x, y): ps) = ps': (cycs ps'')  
                                 where
                                 (ps', ps'') = partOrbit x [(x, y)] ps

  partOrbit  x  orb@((_, y): _)  ps =
    if
       y == x  then  (sortBy (compBy fst) orb, ps)
    else  
    case  span ((/= y) . fst) ps
    of
    (ps', p: ps'') -> partOrbit x (p: orb) (ps' ++ ps'')
    _              -> 
        error $ concat ["ePermutCycles ", shows p "\n... partOrbit ", 
                        shows x " orb ps   failed.\nProbably, the given\
                        \permutation is wrongly represented.\n"]

permutECycles :: Permutation -> [EPermut]
permutECycles =  ePermutCycles . toEPermut

permutCycles :: Permutation -> [[Integer]]
permutCycles =  mapmap snd . ePermutCycles . toEPermut


------------------------------------------------------------------------
allPermuts :: [Integer] -> [Permutation]
                                 -- build the full permutation list
                                 -- given a list * ordered decreasingly*
allPermuts xs = 

  if  not $ isOrderedBy compare $ reverse xs  then
        error $ concat 
        ["\nallPermuts ", shows xs 
         "\n:\nthe argument must be ordered decreasingly.\n"
        ]
  else  map Pm $ pms $ Just xs
        where 
        pms (Just p) = p: (pms $ nextPermut p)
        pms _        = []

test_allPermuts :: [Integer] -> (Integer, Bool, Bool, Bool)
test_allPermuts xs =
  let 
     (n, pms) = (toZ $ length xs, allPermuts xs)
     l        = genLength pms
  in 
  (l, l == factorial n, all isPermut pms, nub pms == pms)

------------------------------------------------------------------------
gensToSemigroupList :: MulSemigroup a => Integer-> [a]-> ([a], Integer)

-- Subsemigroup  sH  generated by the elements  gs.
-- gs  does not contain repetitions.
-- If  |sH| < bound  then the result is  (sH,          |sH|) 
-- otherwise                             (currentList, 0   ).

gensToSemigroupList bound gs =  saturate gs 
  --
  -- add products by  g(i)  until the product set is stable
  where
  saturate xs =
    let
      ys = foldl union xs $ map (g_products xs) gs 
      l  = genLength ys 
      g_products xs g = map (mul g) xs
    in
    case (l < bound, all (`elem` xs) ys) of (False, _   ) -> (ys, 0)
                                            (_,     True) -> (ys, l)
                                            _             -> saturate ys
